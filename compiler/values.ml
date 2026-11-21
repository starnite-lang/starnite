(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Arithmetic and formatting shared by the reference interpreter and constant folding.
   The C runtime implements the same rules; the fuzzer compares the two (section 21.2). *)

open Types

exception Trap of string * Syntax.loc * string   (* kind, location, message *)

let trap kind loc msg = raise (Trap (kind, loc, msg))

let min_of k =
  match k with
  | IInt | I64 -> Int64.min_int
  | I8 -> -128L | I16 -> -32768L | I32 -> -2147483648L
  | U8 | U16 | U32 | U64 -> 0L

let max_of k =
  match k with
  | IInt | I64 -> Int64.max_int
  | I8 -> 127L | I16 -> 32767L | I32 -> 2147483647L
  | U8 -> 255L | U16 -> 65535L | U32 -> 4294967295L
  | U64 -> -1L (* all bits set *)

let fits k v =
  match k with
  | IInt | I64 | U64 -> true
  | _ -> Int64.compare v (min_of k) >= 0 && Int64.compare v (max_of k) <= 0

(* Truncate to the width of k, as the wrapping operators do. *)
let wrap k v =
  match k with
  | IInt | I64 | U64 -> v
  | I8 -> Int64.of_int ((Int64.to_int v land 0xFF lxor 0x80) - 0x80)
  | I16 -> Int64.of_int ((Int64.to_int v land 0xFFFF lxor 0x8000) - 0x8000)
  | I32 -> Int64.of_int32 (Int64.to_int32 v)
  | U8 -> Int64.logand v 0xFFL
  | U16 -> Int64.logand v 0xFFFFL
  | U32 -> Int64.logand v 0xFFFFFFFFL

let overflow loc = trap "integer overflow" loc "the result does not fit its type"

let add k loc a b =
  let r = Int64.add a b in
  match k with
  | IInt | I64 ->
      if Int64.compare a 0L >= 0 = (Int64.compare b 0L >= 0) && Int64.compare r 0L >= 0 <> (Int64.compare a 0L >= 0) then overflow loc;
      r
  | U64 -> if Int64.unsigned_compare r a < 0 then overflow loc; r
  | _ -> if not (fits k r) then overflow loc; r

let sub k loc a b =
  let r = Int64.sub a b in
  match k with
  | IInt | I64 ->
      if Int64.compare a 0L >= 0 <> (Int64.compare b 0L >= 0) && Int64.compare r 0L >= 0 <> (Int64.compare a 0L >= 0) then overflow loc;
      r
  | U64 -> if Int64.unsigned_compare a b < 0 then overflow loc; r
  | _ -> if not (fits k r) then overflow loc; r

let mul k loc a b =
  let r = Int64.mul a b in
  match k with
  | IInt | I64 ->
      if a <> 0L && (Int64.div r a <> b || (a = -1L && b = Int64.min_int) || (b = -1L && a = Int64.min_int)) then overflow loc;
      r
  | U64 -> if a <> 0L && Int64.unsigned_div r a <> b then overflow loc; r
  | I32 | U32 ->
      (* 32-bit operands cannot overflow the 64-bit product *)
      if not (fits k r) then overflow loc; r
  | _ -> if not (fits k r) then overflow loc; r

let div k loc a b =
  if b = 0L then trap "division by zero" loc "the divisor is zero";
  match k with
  | U64 -> Int64.unsigned_div a b
  | _ ->
      if b = -1L && a = min_of k && ikind_signed k then overflow loc;
      Int64.div a b

let rem k loc a b =
  if b = 0L then trap "division by zero" loc "the divisor is zero";
  match k with
  | U64 -> Int64.unsigned_rem a b
  | _ -> if b = -1L then 0L else Int64.rem a b

let compare_int k a b = if k = U64 then Int64.unsigned_compare a b else Int64.compare a b

let int_to_string k v = if k = U64 then Printf.sprintf "%Lu" v else Int64.to_string v

(* Float text (section 20.1): the shortest digits that read back as the same value, in
   fixed notation when the decimal exponent is in [-4, 16), else scientific. The C
   runtime (stn_show_f64) implements the same rule; the backends must agree exactly. *)
let format_digits neg (digits : string) (exp : int) =
  let nd = String.length digits in
  let body =
    if exp >= -4 && exp < 16 then
      if exp >= 0 then
        let ip = if nd > exp + 1 then String.sub digits 0 (exp + 1) else digits ^ String.make (exp + 1 - nd) '0' in
        let fp = if nd > exp + 1 then String.sub digits (exp + 1) (nd - exp - 1) else "0" in
        ip ^ "." ^ fp
      else "0." ^ String.make (-exp - 1) '0' ^ digits
    else
      let m = if nd > 1 then String.sub digits 0 1 ^ "." ^ String.sub digits 1 (nd - 1) else digits in
      Printf.sprintf "%se%c%02d" m (if exp < 0 then '-' else '+') (abs exp)
  in
  (if neg then "-" else "") ^ body

let shortest (f : float) (maxp : int) (roundtrips : string -> bool) =
  if Float.is_nan f then "nan"
  else if f = Float.infinity then "inf"
  else if f = Float.neg_infinity then "-inf"
  else begin
    let rec go p =
      let s = Printf.sprintf "%.*e" (p - 1) f in
      if p >= maxp || roundtrips s then s else go (p + 1)
    in
    let s = go 1 in
    let neg = s.[0] = '-' in
    let s = if neg then String.sub s 1 (String.length s - 1) else s in
    let epos = String.index s 'e' in
    let mant = String.sub s 0 epos in
    let exp = int_of_string (String.sub s (epos + 1) (String.length s - epos - 1)) in
    let digits = String.concat "" (String.split_on_char '.' mant) in
    let n = ref (String.length digits) in
    while !n > 1 && digits.[!n - 1] = '0' do decr n done;
    format_digits neg (String.sub digits 0 !n) exp
  end

let float_to_string (f : float) = shortest f 17 (fun s -> float_of_string s = f)

let f32_round (f : float) = Int32.float_of_bits (Int32.bits_of_float f)

let f32_to_string (f : float) = shortest f 9 (fun s -> f32_round (float_of_string s) = f)

let rec parse_int_lit (s : string) : int64 =
  if String.length s > 0 && s.[0] = '-' then Int64.neg (parse_int_lit (String.sub s 1 (String.length s - 1)))
  else if String.length s > 2 && (s.[1] = 'b' || s.[1] = 'B') then Int64.of_string ("0b" ^ String.sub s 2 (String.length s - 2))
  else try Int64.of_string s with _ -> Int64.of_string ("0u" ^ s)

let dur_value n u =
  match u with
  | "ns" -> n | "us" -> Int64.mul n 1000L | "ms" -> Int64.mul n 1_000_000L | "s" -> Int64.mul n 1_000_000_000L
  | "min" -> Int64.mul n 60_000_000_000L | "h" -> Int64.mul n 3_600_000_000_000L
  | "b" -> n | "kib" -> Int64.mul n 1024L | "mib" -> Int64.mul n 1048576L | "gib" -> Int64.mul n 1073741824L
  | _ -> n

(* Is [s] a well-formed integer for parse_int? Accepts an optional sign and decimal digits. *)
let parse_int_text (s : string) : int64 option =
  let n = String.length s in
  if n = 0 then None
  else begin
    let neg = s.[0] = '-' in
    let st = if s.[0] = '-' || s.[0] = '+' then 1 else 0 in
    if st = n then None
    else begin
      let ok = ref true in
      for i = st to n - 1 do if s.[i] < '0' || s.[i] > '9' then ok := false done;
      if not !ok then None
      else
        (* accumulate negatively to reach min_int *)
        let acc = ref 0L and over = ref false in
        for i = st to n - 1 do
          let d = Int64.of_int (Char.code s.[i] - 48) in
          let next = Int64.sub (Int64.mul !acc 10L) d in
          if Int64.compare !acc (Int64.div Int64.min_int 10L) < 0 || Int64.compare next 0L > 0 then over := true;
          acc := next
        done;
        if !over then Some 0L |> fun _ -> raise Exit
        else if neg then Some !acc
        else if !acc = Int64.min_int then raise Exit
        else Some (Int64.neg !acc)
    end
  end
