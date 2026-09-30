import cosm/mapping

type HoloJson* = object
template eachParent*(group: typedesc[HoloJson], toApply: untyped) =
  toApply Json

type
  Foo {.inheritable.} = object
    a {.mapping: "x".}: string
    case b {.mapping(Json, "y").}: uint8 #range[0..5] # https://github.com/nim-lang/Nim/pull/25585
    of 0..2:
      c {.mapping: "tooGeneral", mapping(Json, "better"), mapping(HoloJson, "z"), mapping(Json, "worse"), mapping: "tooGeneralAgain".}: int
      #when true: # nim limitation
      d {.mapping: "t".}: bool
    else:
      discard
    notRenamed: string

  Bar = ref object of Foo
    e {.mapping: "u".}: int

type
  FooHooked {.inheritable.} = object
    a {.mapping: "x".}: string
    case b {.mapping(Json, "wrong").}: uint8 #range[0..5] # https://github.com/nim-lang/Nim/pull/25585
    of 0..2:
      c {.mapping(HoloJson, "wrong").}: int
      #when true: # nim limitation
      d {.mapping: "wrong".}: bool
    else:
      discard
    notRenamed: string

  BarHooked = ref object of FooHooked
    e {.mapping: "u".}: int

const barHookedMappings = @{
  "a": toFieldMapping "x",
  "b": toFieldMapping "y",
  "c": toFieldMapping "z",
  "d": toFieldMapping "t",
  "e": toFieldMapping "u",
  "notRenamed": FieldMapping()
}

proc getFieldMappings*(foo: typedesc[BarHooked], group: typedesc): FieldMappingPairs =
  barHookedMappings

type UnrefObjHooked = object
  a, b, c: int

const unrefObjHookedMappings = @{
  "a": toFieldMapping ignore(),
  "b": toFieldMapping "x",
  "c": FieldMapping(ignore: IgnoreMapping(input: true), name: NameMapping(output: toName "Foo"))
}

proc getFieldMappings(_: type UnrefObjHooked, group: typedesc): FieldMappingPairs =
  unrefObjHookedMappings

proc `==`(a, b: NamePattern): bool {.noSideEffect.} =
  result = a.kind == b.kind
  if result:
    case a.kind
    of NoName, NameOriginal, NameSnakeCase: discard
    of NameString: result = a.str == b.str
    of NameConcat: result = a.concat == b.concat

block: # test mappings for Bar
  const mappings = getActualFieldMappings(Bar, HoloJson)
  const expected = @{
    "e": toFieldMapping("u"),
    "a": toFieldMapping("x"),
    "b": toFieldMapping("y"),
    "c": toFieldMapping("z"),
    "d": toFieldMapping("t"),
    "notRenamed": FieldMapping()
  }
  doAssert mappings == expected

block: # for BarHooked
  const mappings = getActualFieldMappings(BarHooked, HoloJson)
  doAssert mappings == barHookedMappings
  doAssert mappings == getFieldMappings(BarHooked, HoloJson)

block: # for UnrefObjHooked
  const unrefMappings = getActualFieldMappings(UnrefObjHooked, HoloJson)
  doAssert unrefMappings == unrefObjHookedMappings
  doAssert unrefMappings == getFieldMappings(UnrefObjHooked, HoloJson)
  const refMappings = getActualFieldMappings(ref UnrefObjHooked, HoloJson)
  doAssert refMappings == unrefMappings
