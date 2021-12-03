val filename = List.last (CommandLine.arguments ())
val object = String.substring(filename,0, String.size filename - 4)
val _ = PolyML.make filename;
val _ = PolyML.export (object, main);
val _ = Unix.exit (Word8.fromInt 0)

