## default interpretation for field mapping options

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

proc ignore*(): IgnoreMapping =
  ## creates a field option object that ignores this field in both serialization and deserialization
  IgnoreMapping(input: true, output: true)

proc toNameMapping*(options: NameMapping): NameMapping = options
proc toNameMapping*(name: NamePattern): NameMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a name pattern this sets both the serialization and deserialization name of the field to it
  NameMapping(inputs: @[name], output: name)
proc toNameMapping*(name: string): NameMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a string this sets both the serialization and deserialization name of the field to it
  toNameMapping(toName(name))

proc toIgnoreMapping*(options: IgnoreMapping): IgnoreMapping = options
proc toIgnoreMapping*(enabled: bool): IgnoreMapping =
  IgnoreMapping(input: not enabled, output: not enabled)

proc toNameMapping*(ignoreOptions: bool | IgnoreMapping): NameMapping =
  ## hook to allow for orthogonality with `IgnoreMapping` options, just gives a default name mapping
  NameMapping()

proc toIgnoreMapping*(nameOptions: string | NamePattern | NameMapping): IgnoreMapping =
  ## hook to allow for orthogonality with `NameMapping` options, just gives a default ignore mapping
  IgnoreMapping()

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

proc toNameMapping*(fullOptions: FieldMapping): NameMapping =
  ## hook to allow for narrowing from `FieldMapping`
  fullOptions.name

proc toIgnoreMapping*(fullOptions: FieldMapping): IgnoreMapping =
  ## hook to allow for narrowing from `FieldMapping`
  fullOptions.ignore

type
  FieldMappingPairs* = seq[(string, FieldMapping)]
    # XXX maybe use NimNode for name too to make use of eqIdent performance
  HasFieldMappings* = concept
    ## implement to override mappings for a type
    proc getFieldMappings(obj: typedesc[Self], group: typedesc#[Group]#): FieldMappingPairs
