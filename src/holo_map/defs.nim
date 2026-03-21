type
  Mapping*[Input, Output] = concept
    proc interpret(format: Self, input: Input): Output
  TypeMapping*[Input, Output] = concept
    proc interpret(format: Self, input: Input, output: type Output): Output
  InPlaceMapping*[Input, Output] = concept
    proc interpret(format: Self, input: Input, output: var Output)
  OutParamMapping*[Input, Output] = concept
    proc interpret(format: Self, input: Input, output: out Output)
