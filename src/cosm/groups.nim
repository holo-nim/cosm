## basic definitions for group types
## 
## to define a new group type, it is enough to do `type GroupType = object`
## and fill in the relevant overloads, but this design might not be permanent

type AnyMapping* = object
  ## stand-in for any mapping type

template mapping*(options: typed) {.pragma.}
  ## sets the mapping options for a field for any mapping group
  ##
  ## option can be of any type, which is then interpreted by mapping macros
  ## by wrapping it in a hook i.e. `toFieldMapping`, see the `field_options`
  ## module for the default interpretation
  ## 
  ## irrelevant options should be ignored by hooks for orthogonality,
  ## i.e. a mapping that does not use field names should treat just a name mapping
  ## as if no option was given 

template mapping*[T](group: typedesc[T], options: typed) {.pragma.}
  ## mapping pragma but filtered to the given mapping group,
  ## filters with the least inheritance depth or earliest order are preferred

template eachParent*[T](group: typedesc[T], toApply: untyped) =
  ## passes each parent type of `group` is as a call argument to `toApply`
  ## 
  ## needs to be overloaded to define group parents, 
  ## by default assumes no parent types and does nothing
  # toApply(AnyMapping)
  discard

proc isSubmapping*(A, B: typedesc): bool #[{.compileTime.}]# =
  ## infers if `B` is some parent of `A` depending on `eachParent`
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
