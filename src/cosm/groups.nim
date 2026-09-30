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
