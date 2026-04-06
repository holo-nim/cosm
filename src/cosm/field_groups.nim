import ./[groups, field_options], std/macros, private/macroutils

type HasFieldMappings* = concept
  ## implement to override mappings for a type
  proc getFieldMappings(obj: typedesc[Self], group: static MappingGroup): FieldMappingPairs

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

proc buildFieldMappingPairs*(obj: NimNode, group: MappingGroup): NimNode =
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
  result = newNimNode(nnkBracket, obj)
  for name, prag in names.items:
    var val: NimNode = nil
    var lastFilter = AnyMappingGroup
    if prag != nil and supportsCustomPragma:
      # again copied from macros.customPragma
      for p in prag:
        if p.kind in nnkPragmaCallKinds and p.len > 0 and p[0].kind == nnkSym and matchCustomPragma(p[0]):
          let def = p[0].getImpl[3]
          let arg = if def.len == 3: p[2] else: p[1] 
          let filter = if def.len == 3: getMappingGroupFromLiteral(p[1]) else: AnyMappingGroup
          if group <= filter and filter <= lastFilter:
            val = arg
            lastFilter = filter
          when false:
            if p.len == 2 or
                # ??? generics support?
                (p.len == 3 and p[1].kind == nnkSym and p[1].symKind == nskType):
              val = p[1]
            else:
              let def = p[0].getImpl[3]
              val = newTree(nnkPar)
              for i in 1 ..< def.len:
                let key = def[i][0]
                let val = p[i]
                val.add newTree(nnkExprColonExpr, key, val)
    if val == nil:
      val = quote do: FieldMapping()
    else:
      val = quote do: toFieldMapping(`val`)
    result.add(newTree(nnkTupleConstr,
      newLit(name),
      val))
    when false:
      let ident = ident(name)
      if isTuple:
        quote do:
          FieldMapping()
      else:
        quote do:
          when hasCustomPragma(`obj`.`ident`, `pragmaSym`):
            toFieldMapping(getCustomPragmaVal(`obj`.`ident`, `pragmaSym`))
          else:
            FieldMapping()
  result = newCall(bindSym"@", result)

macro getDefaultFieldMappings*[T: FieldedType](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): FieldMappingPairs =
  result = buildFieldMappingPairs(obj, group)

template getActualFieldMappings*[T: HasFieldMappings](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): FieldMappingPairs =
  mixin getFieldMappings
  getFieldMappings(T, group)

template getActualFieldMappings*[U: HasFieldMappings, T: (ref U) and not HasFieldMappings](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): FieldMappingPairs =
  mixin getFieldMappings
  getFieldMappings(U, group)

template getActualFieldMappings*[T: FieldedType and not HasFieldMappings](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): FieldMappingPairs =
  when T isnot ref and (ref T) is HasFieldMappings:
    mixin getFieldMappings
    getFieldMappings(ref T, group)
  else:
    getDefaultFieldMappings(T, group)
