open ExtLib

let the = Option.get
let sprintf = Printf.sprintf

module String_Key = struct
  type t = string
  let equal = String.equal
  let compare = String.compare
  let hash = Hashtbl.hash
end

let pp_sep_list sep pp f = function
  | [] -> ()
  | hd::tl ->
    pp f hd;
    List.iter (Format.fprintf f "%s%a" sep pp) tl

let pp_comma_sep_list pp f = pp_sep_list ", " pp f
