import cosm/arrays

type Foo = enum a, b, c, d, e, f, g, h, i

const strs: array[c..h, string] = [
  c: "alpha",
  d: "beta",
  e: "gamma",
  f: "delta",
  g: "epsilon",
  h: "zeta"
]

proc translate(s: string): Foo =
  template onKey(foo: Foo): Foo = foo
  arrayInverseCase(strs, s, onKey):
    # else branch
    a

for i, val in strs:
  doAssert translate(val) == i
doAssert translate("nonexistent") == a
