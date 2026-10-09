import std/macros

template arrayInverseCase*[I, T](arr: static array[I, T], value: T, onKey, onElse: untyped): untyped =
  ## generates a case statement that matches `value` against the values of `arr`,
  ## calling `onKey` with the index if it does match a value, and directly inserting
  ## `onElse` to the else block
  macro tempMacro(value2, onKey2, onElse2: untyped): untyped {.gensym.} =
    result = newTree(nnkCaseStmt, value2)
    for index in low(I) .. high(I):
      result.add newTree(nnkOfBranch, newLit(arr[index]), newCall(onKey2, newLit(index)))
    result.add newTree(nnkElse, onElse2)
  tempMacro(value, onKey, onElse)

template arrayInverseCaseExhaustive*[I, T](arr: static array[I, T], value: T, onKey: untyped): untyped =
  ## generates a case statement that matches `value` against the values of `arr`,
  ## calling `onKey` with the index if it does match a value, and no `else` branch
  macro tempMacro(value2, onKey2: untyped): untyped {.gensym.} =
    result = newTree(nnkCaseStmt, value2)
    for index in low(I) .. high(I):
      result.add newTree(nnkOfBranch, newLit(arr[index]), newCall(onKey2, newLit(index)))
  tempMacro(value, onKey)
