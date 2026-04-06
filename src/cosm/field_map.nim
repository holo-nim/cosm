import ./field_options, std/[macros, tables]

proc toUnique[T](x: openArray[T]): seq[T] =
  result = newSeqOfCap[T](x.len)
  for a in x:
    if a notin result:
      result.add(x)

proc isNilAst(n: NimNode): bool =
  n.isNil or n.kind == nnkNilLit or n.eqIdent"nil"

proc wrapNormalizer(normalizer, n: NimNode): NimNode =
  if not isNilAst(normalizer):
    newCall(normalizer, n)
  else:
    n

macro wrapNormalizerMacro(normalizer: typed, n: untyped): untyped =
  result = wrapNormalizer(normalizer, n)

proc addInputNamesToBranch(branch: NimNode, fieldName: string, options: FieldMapping, normalizer: NimNode, defaultInputs: seq[NamePattern]) =
  let inputNames = getInputNames(fieldName, options, defaultInputs)
  if isNilAst(normalizer):
    for name in inputNames:
      branch.add newLit(name)
  else:
    var namesNode = newNimNode(nnkBracket, normalizer)
    for name in inputNames:
      namesNode.add newCall(normalizer, newLit(name))
    branch.add newCall(bindSym"toUnique", namesNode)

macro mapFieldInput*[T: FieldedType](
    v: T, key: string,
    # type of v not used yet but maybe in the future to manually complete `fields` XXX #5
    fields: static FieldMappingPairs,
    normalizer: typed,
    defaultInputs: static seq[NamePattern],
    templToCall, elseBody: untyped): untyped =
  ## calls `templToCall` with the address of the mapped field of `v`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  ##
  ## warning: currently requires importing `std/importutils` and calling `privateAccess` on the object type to work with private fields
  result = newNimNode(nnkCaseStmt, key)
  result.add wrapNormalizer(normalizer, key)
  for fieldName, options in fields.items:
    if not options.input.ignore:
      var branch = newTree(nnkOfBranch)
      addInputNamesToBranch(branch, fieldName, options, normalizer, defaultInputs)
      branch.add newCall(templToCall, newDotExpr(copy v, ident fieldName))
      #branch.add crudeReplaceIdent(body, "field", newDotExpr(copy v, ident fieldName))
      result.add branch
  if result.len == 1:
    result = newTree(nnkDiscardStmt, newEmptyNode())
  else:
    result.add newTree(nnkElse, elseBody)

import ./variants

macro mapInputVariantFieldName*[T: VariantType](
    obj: typedesc[T], key: string,
    fields: static FieldMappingPairs,
    normalizer: typed,
    defaultInputs: static seq[NamePattern],
    innerFieldTempl, variantFieldTempl, elseBody: untyped) =
  ## finds the variant field name for `key` based on `variants`:
  ## if `key` maps to a variant discriminator, calls `variantFieldTempl` with an identifier of the original field
  ## if `key` maps to a field inside a variant branch, calls `innerFieldTempl` with:
  ##   1. the original field identifier of `key`
  ##   2. the original identifier of the variant field
  ##   3. the first acceptable value of the variant field for the branch that the inner field is in
  ## otherwise, emits `elseBody`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  result = newNimNode(nnkCaseStmt, key)
  result.add wrapNormalizer(normalizer, key)
  let variants = buildVariants(obj)
  let mappingTable = toTable fields
  if variants.variants.len == 0:
    error("got no object variants", obj)
  for variant in variants.variants:
    block variantField:
      let options = mappingTable.getOrDefault(variant.discrimName, FieldMapping())
      if not options.input.ignore:
        var branch = newNimNode(nnkOfBranch, variantFieldTempl)
        addInputNamesToBranch(branch, variant.discrimName, options, normalizer, defaultInputs)
        branch.add newCall(variantFieldTempl, ident variant.discrimName)
        result.add branch
    for fieldName, branchIndex in variant.fieldsToBranch:
      let options = mappingTable.getOrDefault(fieldName, FieldMapping())
      if not options.input.ignore:
        var branch = newNimNode(nnkOfBranch, variantFieldTempl)
        addInputNamesToBranch(branch, fieldName, options, normalizer, defaultInputs)
        let discrimValue = firstValue(variant.branches[branchIndex])
        branch.add newCall(innerFieldTempl,
          ident fieldName,
          ident variant.discrimName,
          copy discrimValue)
        result.add branch
  if result.len == 1:
    result = newTree(nnkDiscardStmt, newEmptyNode())
  else:
    result.add newTree(nnkElse, elseBody)

template mapInputVariantField*[T: VariantType](
    obj: T, key: string,
    fields: static FieldMappingPairs,
    normalizer: typed,
    defaultInputs: static seq[NamePattern],
    innerFieldTempl, variantFieldTempl, elseBody: untyped) =
  ## finds the variant for `key` in `obj`:
  ## if `key` is a variant discriminator, calls `variantFieldTempl` with the address of `key` in `obj`
  ## if `key` is a field inside a variant branch, calls `innerFieldTempl` with:
  ##   1. the address of `key` in `obj`
  ##   2. the address of the variant field
  ##   3. the first acceptable value of the variant field for the branch that the inner field is in
  ## otherwise, emits `elseBody`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  template onInnerField(f, discrimName, discrimValue) =
    `innerFieldTempl`(`obj`.`f`, `obj`.`discrimName`, `discrimValue`)
  template onVariantField(f) =
    `variantFieldTempl`(`obj`.`f`)
  mapInputVariantFieldName(T, key, fields, normalizer, defaultInputs, onInnerField, onVariantField, elseBody)

template mapFieldOutput*[T: FieldedType](
    v: T,
    fields: static FieldMappingPairs,
    normalizer: typed,
    defaultOutput: static NamePattern,
    templToCall: untyped): untyped =
  ## calls `templToCall` with: 1. the mapped field address from `v`, 2. the mapped field name
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  const fieldTable = toTable fields
  for k, e in fieldPairs(when T is ref: v[] else: v):
    const options = fieldTable.getOrDefault(k)
    when not options.output.ignore:
      const outputName = wrapNormalizerMacro(normalizer, getOutputName(k, options, defaultOutput))
      templToCall(e, outputName)

macro mapEnumFieldInput*[T: enum](
  t: typedesc[T], s: string,
  mappings: static FieldMappingPairs,
  normalizer: typed,
  templToCall, elseBody: untyped) =
  ## calls `templToCall` with the mapped enum field from `s`, emits `elseBody` if no such enum field exists
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  # XXX missing default arg because of enum string value #6
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
  if impl.kind != nnkEnumTy:
    error "expected enum type for type impl of " & repr(t), impl
  let mappingTable = toTable(mappings)
  result = newNimNode(nnkCaseStmt, s)
  result.add wrapNormalizer(normalizer, s)
  for f in impl:
    # copied from std/enumutils.genEnumCaseStmt
    var fieldSym: NimNode = nil
    var fieldStrNodes: seq[NimNode] = @[]
    case f.kind
    of nnkEmpty: continue # skip first node of `enumTy`
    of nnkSym, nnkIdent, nnkAccQuoted, nnkOpenSymChoice, nnkClosedSymChoice:
      fieldSym = f
    of nnkEnumFieldDef:
      fieldSym = f[0]
      case f[1].kind
      of nnkStrLit .. nnkTripleStrLit:
        fieldStrNodes = @[f[1]]
      of nnkTupleConstr:
        fieldStrNodes = @[f[1][1]]
      of nnkIntLit:
        discard
      else:
        let fAst = f[0].getImpl
        if fAst != nil:
          case fAst.kind
          of nnkStrLit .. nnkTripleStrLit:
            fieldStrNodes = @[fAst]
          of nnkTupleConstr:
            fieldStrNodes = @[fAst[1]]
          else: discard
    else: error("Invalid node for enum type `" & $f.kind & "`!", f)
    let fieldName = $fieldSym
    let mapping = mappingTable.getOrDefault(fieldName, FieldMapping())
    if hasInputNames(mapping):
      for inputName in mapping.input.names:
        fieldStrNodes.add newLit apply(inputName, fieldName)
    elif fieldStrNodes.len == 0:
      fieldStrNodes = @[newLit fieldName]
    var branch = newTree(nnkOfBranch)
    if not isNilAst(normalizer):
      var namesNode = newNimNode(nnkBracket, normalizer)
      for strNode in fieldStrNodes:
        namesNode.add newCall(normalizer, strNode)
      branch.add newCall(bindSym"toUnique", namesNode)
    else:
      branch.add fieldStrNodes
    branch.add newCall(templToCall, newDotExpr(t, fieldSym))
    result.add branch
  result.add(newTree(nnkElse, elseBody))

macro mapEnumFieldOutput*[T: enum](
  t: typedesc[T], v: T,
  mappings: static FieldMappingPairs,
  normalizer: typed,
  templToCall: untyped) =
  ## calls `templToCall` with the mapped field name of `v`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  # XXX missing default arg because of enum string value #6
  var impl = getTypeInst(v)
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
  if impl.kind != nnkEnumTy:
    error "expected enum type for type impl of " & repr(t), impl
  let mappingTable = toTable(mappings)
  result = newNimNode(nnkCaseStmt, v)
  result.add v
  for f in impl:
    # copied from std/enumutils.genEnumCaseStmt
    var fieldSym, fieldStrNode: NimNode = nil
    case f.kind
    of nnkEmpty: continue # skip first node of `enumTy`
    of nnkSym, nnkIdent, nnkAccQuoted, nnkOpenSymChoice, nnkClosedSymChoice:
      fieldSym = f
    of nnkEnumFieldDef:
      fieldSym = f[0]
      case f[1].kind
      of nnkStrLit .. nnkTripleStrLit:
        fieldStrNode = f[1]
      of nnkTupleConstr:
        fieldStrNode = f[1][1]
      of nnkIntLit:
        discard
      else:
        let fAst = f[0].getImpl
        if fAst != nil:
          case fAst.kind
          of nnkStrLit .. nnkTripleStrLit:
            fieldStrNode = fAst
          of nnkTupleConstr:
            fieldStrNode = fAst[1]
          else: discard
    else: error("Invalid node for enum type `" & $f.kind & "`!", f)
    let fieldName = $fieldSym
    let mapping = mappingTable.getOrDefault(fieldName, FieldMapping())
    if hasOutputName(mapping):
      fieldStrNode = newLit apply(mapping.output.name, fieldName)
    elif fieldStrNode == nil or fieldStrNode.kind notin {nnkStrLit..nnkTripleStrLit}:
      fieldStrNode = newLit fieldName
    fieldStrNode = wrapNormalizer(normalizer, fieldStrNode)
    result.add newTree(nnkOfBranch,
      newDotExpr(t, fieldSym),
      newCall(templToCall, fieldStrNode))
  # else branch not allowed anyway
