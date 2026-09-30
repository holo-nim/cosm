## predefined common formats

type Binary* = object
template mimeType*(_: type Binary): string = "application/octet-stream"

type Json* = object
template mimeType*(_: type Json): string = "application/json"
