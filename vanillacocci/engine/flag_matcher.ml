let debug_engine = ref false
let verbose_matcher = ref true


(* false = simpler formulas, only for debugging *)
let useEU = ref true

let disallow_nested_exps = ref false

(* if this flag is not set, then break and continue are also error exits *)
let only_return_is_error_exit = ref false

(* a hack to allow adding code in some more sgrep-like uses *)
let allow_inconsistent_paths = ref false

(* see the use of this variable in asttoctl2.ml *)
let no_safe_expressions = ref false

let show_misc = ref true


let show_transinfo = ref false
