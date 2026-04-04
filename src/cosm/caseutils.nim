import std/strutils

iterator splitWordsCamelCase*(s: string, uncapitalized: bool = false): string =
  if s.len != 0:
    var current: string
    if uncapitalized: current = $toLowerAscii(s[0])
    else: current = $s[0]
    var i = 1
    while i < s.len:
      var c = s[i]
      if isUpperAscii(c):
        c = toLowerAscii(c)
        if isLowerAscii(s[i-1]) or (i + 1 < s.len and isLowerAscii(s[i+1])):
          yield current
          current = $c
        else:
          current.add(c)
      elif c in Whitespace:
        if current.len != 0:
          yield current
          current = ""
      elif c == '_':
        if current.len != 0:
          yield current
          current = ""
      else:
        current.add(c)
      inc i
    if current.len != 0:
      yield current

proc toSnakeCase*(s: string, uncapitalized = false): string =
  result = ""
  for word in splitWordsCamelCase(s, uncapitalized):
    if result.len != 0: result.add '_'
    result.add word

proc toKebabCase*(s: string, uncapitalized = false): string =
  result = ""
  for word in splitWordsCamelCase(s, uncapitalized):
    if result.len != 0: result.add '-'
    result.add word
