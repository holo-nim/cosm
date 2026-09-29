import std/macros, private/macroutils

# --- mapping definitions ---

type AnyMapping* = object
  ## stand-in for any mapping type

template mapping*(options: typed) {.pragma.}
  ## sets the mapping options for a field

template mapping*[T](group: typedesc[T], options: typed) {.pragma.}
  ## sets the mapping options for a field
  ## filtered to formats encompassed by the given mapping group

template eachParent*[T](group: typedesc[T], toApply: untyped) =
  ## overload so that each parent type of `group` is passed as an argument to `toApply`,
  ## by default assumes no parent types and does nothing
  # toApply(AnyMapping)
  discard

proc isSubmapping*(A, B: typedesc): bool #[{.compileTime.}]# =
  when B is AnyMapping:
    result = true
  elif A is B:
    result = true
  else:
    mixin eachParent
    result = false
    template checkParent(parent) {.used.} =
      if isSubmapping(parent, B): return true
    eachParent(A, checkParent)

# --- mapping pragma behavior ---

proc iterFieldNames(names: var seq[(string, NimNode)], list: NimNode) =
  case list.kind
  of nnkRecList, nnkTupleTy:
    for r in list:
      iterFieldNames(names, r)
  of nnkRecCase:
    iterFieldNames(names, list[0])
    for bi in 1 ..< list.len:
      expectKind list[bi], {nnkOfBranch, nnkElifBranch, nnkElse}
      iterFieldNames(names, list[bi][^1])
  of nnkRecWhen:
    for bi in 0 ..< list.len:
      expectKind list[bi], {nnkElifBranch, nnkElse}
      iterFieldNames(names, list[bi][^1])
  of nnkIdentDefs:
    for i in 0 ..< list.len - 2:
      let name = realBasename(list[i])
      var prag: NimNode = nil
      if list[i].kind == nnkPragmaExpr:
        prag = list[i][1]
      block doAdd:
        for existing in names.mitems:
          if existing[0] == name:
            break doAdd
        names.add (name, prag)
  of nnkSym:
    when defined(holomapSymPragmaWarning):
      warning "got just sym for object field, maybe missing pragma information", list
    let name = $list
    names.add (name, nil)
  of nnkDiscardStmt, nnkNilLit, nnkEmpty: discard
  else:
    error "unknown object field AST kind " & $list.kind, list

const
  nnkPragmaCallKinds = {nnkExprColonExpr, nnkCall, nnkCallStrLit}

proc matchCustomPragma(sym: NimNode): bool =
  result = sym.kind == nnkSym and sym.eqIdent"mapping"
  if result:
    let impl = getImpl(sym)
    result = impl != nil and impl.kind == nnkTemplateDef

proc stripTypeNode(t: NimNode): NimNode =
  if t.isNil: return t
  result = getTypeInst(t)
  while true:
    if result.kind in {nnkRefTy, nnkPtrTy, nnkVarTy, nnkOutTy}:
      if result[^1].kind == nnkObjectTy:
        result = result[^1]
      else:
        result = getTypeInst(result[^1])
    elif result.kind == nnkBracketExpr and result[0].eqIdent"typeDesc":
      result = getTypeInst(result[1])
    elif result.kind == nnkBracketExpr and result[0].kind == nnkSym:
      break
    elif result.kind == nnkSym:
      break
    else:
      break

proc matchTypeNodesStripped(a, b: NimNode): bool =
  if a.isNil or b.isNil:
    result = a.isNil and b.isNil
  else:
    result = sameType(a, b)

type
  FieldMappingFilter* = object
    group*: NimNode
    parents*: seq[FieldMappingFilter]

proc prestrip(filter: FieldMappingFilter): FieldMappingFilter =
  result = FieldMappingFilter()
  result.group = stripTypeNode(filter.group)
  for parent in filter.parents:
    result.parents.add prestrip(parent) 

proc matchPrestripped(filter: FieldMappingFilter, group: NimNode): int =
  ## returns depth, -1 if no match
  if matchTypeNodesStripped(filter.group, group):
    result = 0
  else:
    result = -1
    for p in filter.parents:
      let parentMatch = p.matchPrestripped(group)
      if parentMatch >= 0:
        let branch = parentMatch + 1
        if result < 0 or branch < result:
          result = branch
          if result == 1:
            return

iterator fieldMappingNodes(obj: NimNode, filter: FieldMappingFilter): tuple[field: string, mapping: NimNode] =
  ## looks for mapping pragmas of the fields of `obj` matching the group filter
  var names: seq[(string, NimNode)] = @[]
  var t = obj
  var supportsCustomPragma = false
  while t != nil:
    # very horribly try to copy macros.customPragma:
    var impl = getTypeInst(t)
    while true:
      if impl.kind in {nnkRefTy, nnkPtrTy, nnkVarTy, nnkOutTy}:
        if impl[^1].kind == nnkObjectTy:
          impl = impl[^1]
        else:
          impl = getTypeInst(impl[^1])
      elif impl.kind == nnkBracketExpr and impl[0].eqIdent"typeDesc":
        impl = getTypeInst(impl[1])
      elif impl.kind == nnkBracketExpr and impl[0].kind == nnkSym:
        impl = getImpl(impl[0])[^1]
      elif impl.kind == nnkSym:
        impl = getImpl(impl)[^1]
      else:
        break
    case impl.kind
    of nnkTupleTy:
      supportsCustomPragma = false
      iterFieldNames(names, impl)
      t = nil
    #of nnkEnumTy:
    #  supportsCustomPragma = false
    #  t = nil
    of nnkObjectTy:
      supportsCustomPragma = true
      iterFieldNames(names, impl[^1])
      t = nil
      if impl[1].kind != nnkEmpty:
        expectKind impl[1], nnkOfInherit
        t = impl[1][0]
    else:
      error "got unknown object type kind " & $impl.kind, impl
  let prestripped = prestrip(filter)
  for name, prag in names.items:
    var val: NimNode = nil
    var lastDepth = -1
    if prag != nil and supportsCustomPragma:
      # again copied from macros.customPragma
      for p in prag:
        if p.kind in nnkPragmaCallKinds and p.len > 0 and p[0].kind == nnkSym and matchCustomPragma(p[0]):
          let def = p[0].getImpl[3]
          let arg = if def.len == 3: p[2] else: p[1]
          let group = if def.len == 3: p[1] else: nil
          let depth =
            if group.isNil:
              if prestripped.group.isNil: 0
              else: high(int)
            else: matchPrestripped(prestripped, stripTypeNode(group))
          if depth >= 0 and (lastDepth < 0 or depth < lastDepth):
            val = arg
            lastDepth = depth
            if depth == 0:
              break
    yield (name, val)

proc buildFieldMappingPairsNode(obj: NimNode, filter: FieldMappingFilter, callWrap: NimNode, missing: NimNode): NimNode =
  ## from `fieldMappingNodes`, builds an array literal of tuples of
  ## 1. the field name string,
  ## 2. the mapping node wrapped in a call to `callWrap` if mapping exists, otherwise the node `missing`
  result = newNimNode(nnkBracket, obj)
  for fieldName, mappingNode in fieldMappingNodes(obj, filter):
    result.add(newTree(nnkTupleConstr,
      newLit(fieldName),
      if mappingNode.isNil: missing else: newCall(callWrap, mappingNode)))

proc groupFilterNode(group: typedesc): FieldMappingFilter =
  when group is AnyMapping:
    result = FieldMappingFilter(group: nil, parents: @[])
  else:
    mixin eachParent
    result = FieldMappingFilter(group: getTypeInst(group), parents: @[])
    template addParent(parent: untyped) {.used.} =
      result.parents.add groupFilterNode(parent)
    eachParent(group, addParent)

type FieldedType* = (object | ref object | tuple)
  # XXX also maybe enum

template buildFieldMappingPairs*[T: FieldedType](obj: typedesc[T], group: typedesc, callWrap: untyped, missing: untyped): untyped =
  ## looks for mapping pragmas of the fields of `obj` for `group`,
  ## where `group = AnyMapping` represents no filter
  ## 
  ## then returns an array literal of tuples of
  ## 1. the field name string,
  ## 2. the mapping node wrapped in a call to `callWrap` if mapping provided, otherwise the node `missing`
  macro intermediate(obj2, callWrap2, missing2: untyped): untyped =
    let filter = groupFilterNode(group)
    result = buildFieldMappingPairsNode(obj2, filter, callWrap2, missing2)
  intermediate(obj, callWrap, missing)

# --- default mapping types ---

import ./caseutils

type
  NamePatternKind* = enum
    NoName,
    NameOriginal, ## uses the field name
    NameString, ## uses custom string and ignores field name
    NameSnakeCase ## converts field name to snake case
    # maybe raw name like unquoted json
    NameConcat
  NamePattern* = object
    ## string pattern to apply to a given field name to use in mapping
    case kind*: NamePatternKind
    of NoName: discard
    of NameOriginal: discard
    of NameString: str*: string
    of NameSnakeCase: discard
    of NameConcat: concat*: seq[NamePattern]
  NameMapping* = object
    inputs*: seq[NamePattern]
      ## names that are accepted for this field when encountered in input
      ## if none are given, a default set of names can be used instead
    output*: NamePattern
      ## name for this field in output
      ## if not given or set to `NoName`, a default name can be used instead
    # maybe normalize case option - needs to be done for the type overall
  IgnoreMapping* = object
    input*: bool
      ## whether or not to ignore a field when encountered in input
    output*: bool
      ## whether or not to ignore a field when generating output
  FieldMapping* = object
    ## mapping options for a type field
    name*: NameMapping
    ignore*: IgnoreMapping

proc toName*(str: string): NamePattern =
  ## creates a name pattern that uses a specific string instead of the field name
  NamePattern(kind: NameString, str: str)

proc snakeCase*(): NamePattern =
  ## creates a name pattern that just converts a field name to snake case
  NamePattern(kind: NameSnakeCase)

proc verbatim*(): NamePattern =
  NamePattern(kind: NameOriginal)

proc apply*(pattern: NamePattern, name: string): string =
  ## applies a name pattern to a given name
  case pattern.kind
  of NoName:
    result = ""
  of NameOriginal:
    result = name
  of NameString:
    result = pattern.str
  of NameSnakeCase:
    result = toSnakeCase(name)
  of NameConcat:
    if pattern.concat.len == 0: return ""
    result = apply(pattern.concat[0], name)
    for i in 1 ..< pattern.concat.len: result.add apply(pattern.concat[i], name)

proc toNameMapping*(options: NameMapping): NameMapping = options
proc toNameMapping*(name: NamePattern): NameMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a name pattern this sets both the serialization and deserialization name of the field to it
  NameMapping(inputs: @[name], output: name)
proc toNameMapping*(name: string): NameMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a string this sets both the serialization and deserialization name of the field to it
  toNameMapping(toName(name))

proc ignore*(): IgnoreMapping =
  ## creates a field option object that ignores this field in both serialization and deserialization
  IgnoreMapping(input: true, output: true)

proc toIgnoreMapping*(options: IgnoreMapping): IgnoreMapping = options
proc toIgnoreMapping*(enabled: bool): IgnoreMapping =
  IgnoreMapping(input: not enabled, output: not enabled)

proc toFieldMapping*(options: FieldMapping): FieldMapping = options

proc toFieldMapping*(name: NameMapping): FieldMapping =
  FieldMapping(name: name)

proc toFieldMapping*(name: NamePattern): FieldMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a name pattern this sets both the serialization and deserialization name of the field to it
  toFieldMapping(toNameMapping(name))

proc toFieldMapping*(name: string): FieldMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a string this sets both the serialization and deserialization name of the field to it
  toFieldMapping(toNameMapping(name))

proc toFieldMapping*(ignore: IgnoreMapping): FieldMapping =
  FieldMapping(ignore: ignore)

proc toFieldMapping*(enabled: bool): FieldMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a bool this sets whether or not to enable serialization and deserialization for this field
  toFieldMapping(toIgnoreMapping(enabled))

proc hasInputNames*(options: NameMapping): bool =
  options.inputs.len != 0

proc getInputNames*(fieldName: string, options: NameMapping, default: seq[NamePattern]): seq[string] =
  ## gives the names accepted for this field when encountered in input
  ## if none are given, this defaults to the patterns in `default`
  result = @[]
  let names = if hasInputNames(options): options.inputs else: default
  for pat in names:
    let name = apply(pat, fieldName)
    if name notin result: result.add name

proc hasOutputName*(options: NameMapping): bool =
  options.output.kind != NoName

proc getOutputName*(fieldName: string, options: NameMapping, default: NamePattern): string =
  ## gives the name for this field in output
  ## if not given, this defaults to the pattern in `default`
  let name = if hasOutputName(options): options.output else: default
  result = apply(name, fieldName)

type
  FieldMappingPairs* = seq[(string, FieldMapping)]
    # XXX maybe use NimNode for name too to make use of eqIdent performance
  HasFieldMappings* = concept
    ## implement to override mappings for a type
    proc getFieldMappings(obj: typedesc[Self], group: typedesc#[Group]#): FieldMappingPairs

proc getDefaultFieldMappings*[T: FieldedType](obj: typedesc[T], group: typedesc): FieldMappingPairs #[{.compileTime.}]# =
  result = @(buildFieldMappingPairs(obj, group, toFieldMapping, FieldMapping()))

template derefType[T](_: typedesc[ref T]): typedesc[T] = T

template getActualFieldMappings*[T](obj: typedesc[T], group: typedesc): FieldMappingPairs =
  mixin getFieldMappings
  when T is HasFieldMappings:
    getFieldMappings(T, group)
  elif T is ref:
    when derefType(T) is HasFieldMappings:
      getFieldMappings(derefType(T), group)
    else:
      getDefaultFieldMappings(T, group)
  else:
    when (ref T) is HasFieldMappings:
      getFieldMappings(ref T, group)
    else:
      getDefaultFieldMappings(T, group)
