## a flexible way to extract field options from type field pragmas

import ./groups, std/macros, private/macroutils

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
