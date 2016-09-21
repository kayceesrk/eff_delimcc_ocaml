(* Queens problem from Eff 3.1 *)

(* Eff 3.1 code

type choice = effect
  operation fail : unit -> empty
  operation decide : unit -> bool
end

let c = new choice
let fail () = match c#fail () with

let choose_left =
    handler
    | c#decide () k -> k true

let choose_max =
    handler
    | c#decide () k -> max (k true) (k false)

let choose_all =
    handler
    | val x -> [x]
    | c#fail () _ -> []
    | c#decide () k -> (k true) @ (k false)

;;

(* Try also "choose_max" and "choose_all" *)
with choose_left handle
  let x = (if c#decide () then 10 else 20) in
  let y = (if c#decide () then 0 else 5) in
  x - y

;;

let rec choose_int m n =
  if m > n then
    fail ()
  else if c#decide () then
    m
  else
    choose_int (m + 1) n


let backtrack = handler
| c#decide () k ->
    handle k false with
    | c#fail () _ -> k true

;;

let rec choose xs =
  match xs with
  | [] -> fail ()
  | x :: xs -> if c#decide () then x else choose xs

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y');;

let available x qs =
  filter (fun y -> forall (no_attack (x, y)) qs) [1; 2; 3; 4; 5; 6; 7; 8];;

let rec place x qs =
  if x = 9 then qs else
  let y = choose (available x qs) in
  place (x + 1) ((x, y) :: qs)

let backtrack = handler
| c#decide () k ->
    handle k true with
    | c#fail () _ -> k false

;;

with backtrack handle
  place 1 []


;nt) list = [(8, 4); (7, 2); (6, 7); (5, 3); (4, 6); (3, 8);
(2, 5); (1, 1)]

*)

open Delimcc;;

type empty

type 'eff result = Done | Eff of 'eff

(* Communication channel for the result *)
type 'a result_value = 'a option ref
let get_result : 'a result_value -> 'a = fun r ->
  match !r with
    Some x -> r := None; (* GC *) x

let handle_it:
    'a result prompt ->                     (* effect instance *)
    (unit -> 'w) ->                         (* expression *)
    ('w result_value -> 'a result -> 'c) -> (* handler *)
    'c = fun effectp exp handler ->
  let res = ref None in
  handler res (push_prompt effectp @@ fun () ->
    res := Some (exp ());
    Done)

type choice =
  | Fail of unit * (empty -> choice result)
  | Decide of unit  * (bool -> choice result)


let c = new_prompt ()

let fail () = match
  shift0 c (fun k -> Eff (Fail ((),k))) with _ -> failwith "unreachable"
let decide p arg = shift0 p (fun k -> Eff (Decide (arg,k)))


let rec choose_left res = function
  | Done -> get_result res
  | Eff Decide ((),k) -> choose_left res @@ k true

let rec choose_max res = function
  | Done -> get_result res
  | Eff Decide ((),k) -> max (choose_max res @@ k true)
                             (choose_max res @@ k false)

let rec choose_all res = function
  | Done -> [get_result res]
  | Eff Fail ((),_)   -> []
  | Eff Decide ((),k) -> (choose_all res @@ k true) @
                         (choose_all res @@ k false)

;;

(*
let _ = handle_it c
 (fun () ->
  let x = (if decide c () then 10 else 20) in
  let y = (if decide c () then 0 else 5) in
  x - y)
 choose_left
;;
*)

(* Almost the same syntax as Eff *)
let rec choose xs =
  match xs with
  | [] -> fail ()
  | [x] -> x
  | x :: xs -> if decide c () then x else choose xs

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let available x qs l =
  List.filter (fun y -> List.for_all (no_attack (x, y)) qs) l

let rec place x qs n =
  let l = ref [] in
  for i = n downto 1 do
    l := i::!l;
  done;
  let rec loop x qs =
    if x = n+1 then qs
    else
    let y = choose (available x qs !l) in
    loop (x + 1) ((x, y) :: qs)
  in
  loop x qs


(* This is quite inefficient, but it faithfully represents
   the Eff code, with the relay of the Fail effect.
   The better version, which also lets us efficiently cout all
   solutions, should use separate Decide and Fail effects.
 *)
let rec backtrack res = function
  | Done -> get_result res
  | Eff Fail ((),_) -> fail ()
  | Eff Decide ((),k) ->
      handle_it c (fun () -> backtrack res @@ k true) (fun res1 ->
        let rec loop = function
          | Done -> get_result res1
          | Eff Fail ((),_) -> backtrack res @@ k false
        in loop)
;;

module Benchmark = struct
  let get_mean_sd l =
    let get_mean l = (List.fold_right (fun a v -> a +. v) l 0.) /.
                (float_of_int @@ List.length l)
    in
    let mean = get_mean l in
    let sd = get_mean @@ List.map (fun v -> abs_float (v -. mean) ** 2.) l in
    (mean, sd)

  let benchmark n f =
    let rec run acc = function
    | 0 -> acc
    | n ->
        let t1 = Unix.gettimeofday () in
        let () = f () in
        let d = Unix.gettimeofday () -. t1 in
        run (d::acc) (n-1)
    in
    let r = run [] n in
    get_mean_sd r
end


let main () =
  let n =
    if Array.length Sys.argv > 1
    then int_of_string Sys.argv.(1)
    else 8
  in
  handle_it c (fun () ->
  ignore (place 1 [] n))
 backtrack

let (m,sd) = Benchmark.benchmark 5 main

let _ = Printf.printf "queens_delimcc: \t mean = %f, sd = %f\n%!" m sd

;;
