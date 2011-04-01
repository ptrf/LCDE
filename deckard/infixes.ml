(* in order for infixes to work, we need to open this in every file where
 * infixed are used... *)

module C = Charv

let ( +: ) = C.(+:)

let ( +> ) o f = f o
