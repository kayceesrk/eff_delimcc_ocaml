(*           Encoding of Eff in Ocaml+delimcc            *)
(*
   -- representing the Eff roughly in the same form and shape
   -- dynamic instatiation of effects, with full polymorphism
   -- The default, dynamically instatiated handlers are not
      special in any way
*)


(*
#directory "/home/oleg/Cache/ncaml4/caml-shift";;
#load "delimcc.cma";;
*)

open Delimcc;;

(* Eff code

type 'a nondeterminism =
effect
  operation fail : unit -> empty
  operation choose : ('a * 'a) -> 'a
  operation cow : 'a -> 'a
end
*)

type empty

(* This is the first representation of Eff's nondeterminism effect.
   There are two parameters: 'a is the type of data to choose from.
   'w is the result type of the compuattion.
   Currently, the result type contaminates the effect declaration,
   and will cause the problems later (the inability to handle the same
   effects in different contexts.
*)

type ('a,'w) nondet = 
  | Done   of 'w
  | Fail   of unit * (empty -> ('a,'w) nondet)
  | Choose of ('a * 'a) * ('a -> ('a,'w) nondet)
  | Cow    of 'a * ('a -> ('a,'w) nondet)

(* Sugar for sending effects. Notice how regular the sugar is. 
   See the inferred types.
*)
let choose p arg = shift0 p (fun k -> Choose (arg,k))
let fail p arg   = shift0 p (fun k -> Fail (arg,k))
let cow p arg    = shift0 p (fun k -> Cow (arg,k))


(* Eff code: instantiate the effect signature.

let r = new nondeterminism ;;
*)

let r = new_prompt ();;

(* Eff code

let f () =
  let x = r#choose ("a", "b") in
  print_string x ;
  let y = r#choose ("c", "d") in
  print_string y
;;
*)

let f () =
  let x = choose r ("a","b") in
  Printf.printf "x is %s\n" x;
  let y = choose r ("c","d") in
  Printf.printf "y is %s\n" y;
;;

(* Eff code

let test1 = 
handle
  f ()
with
  | val x -> x
  | r#choose (x, y) k -> k x ; k y
  | r#fail () _ -> ()
*)

(* Check the output *)
let test1 =
  let rec handle = function 
    | Done x -> x
    | Choose ((x,y),k) -> handle (k x); handle (k y)
    | Fail (x,k) -> ()
  in handle (push_prompt r (fun () -> Done (f ())))
;;

(* There is a bit of dissatisfaction. First, handling is described 
   before the expression. The answer-type contaminates. There is a bit
   of boilerplate. Let's fix the problems.
*)

(* Better effect declaration, without the answertype. *)

type 'eff result = Done | Eff of 'eff

type 'a nondet = 
  | Fail   of unit * (empty -> 'a nondet result)
  | Choose of ('a * 'a) * ('a -> 'a nondet result)
  | Cow    of 'a * ('a -> 'a nondet result)


(* Sugar for sending effects. Notice how regular the sugar is. 
   See the inferred types.
*)
let choose p arg = shift0 p (fun k -> Eff (Choose (arg,k)))
let fail p arg   = shift0 p (fun k -> Eff (Fail (arg,k)))
let cow p arg    = shift0 p (fun k -> Eff (Cow (arg,k)))

let r = new_prompt ();;

let f () =
  let x = choose r ("a","b") in
  Printf.printf "x is %s\n" x;
  let y = choose r ("c","d") in
  Printf.printf "y is %s\n" y;
;;

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

(* Now, our code is quite similar to the Eff code *)
let test1 =
  handle_it r f @@ fun res ->
  let rec handler = function 
    | Done  -> get_result res
    | Eff Choose ((x,y),k) -> handler (k x); handler (k y)
    | Eff Fail (x,k) -> ()
  in handler
;;

(* Eff code

let test2 =
handle
  f ()
with
 | r#choose (x, y) k -> k x
;;
*)
let test2 = handle_it r f @@ fun res ->
  let rec handler = function 
    | Done -> get_result res
    | Eff Choose ((x,y),k) -> handler (k x)
  in handler
;;
(*
x is a
y is c
val test2 : unit = ()
*)


(* Eff code

let s = new nondeterminism ;;
let test3 =
handle
  let a = s#choose (1, 2) in
  3 * a
with
| val x -> 10 * x
| s#choose (x, y) k -> k x + 1000 * k y
;;
*)

let s = new_prompt ()
let test3 = handle_it s
  (fun () ->
    let a = choose s (1,2) in
    3 * a
  )
  (fun res ->
  let rec handler = function 
    | Done -> 10 * get_result res
    | Eff Choose ((x,y),k) -> handler (k x) + 1000 * handler (k y)
  in handler)
;;
(* val test3 : int = 60030 *)

(* Eff code: nested handlers

let test4 =
  let p = new nondeterminism in
  handle
    let a = p#choose (1, 2) in
    handle
      let b = p#choose (10, 20) in
      let c = p#cow 3 in
        (a, b, c)
    with
    | val v -> [v]
    | p#cow x k -> k (3 * x)
    | p#choose (x,y) k -> k x @ k y
  with
  | val v -> [v]
  | p#choose (x,y) k -> k x @ k y
;;
*)

(* Notice how closely our code corresponds to the Eff code *)

let test4 =
  let p = new_prompt () in
  handle_it p
  (fun () ->
    let a = choose p (1,2) in
    handle_it p (fun () -> 
      let b = choose p (10,20) in
      let c = cow p 3 in
     (a,b,c))
   (fun res -> (* inner handler *)
     let rec handler = function
       | Done -> [get_result res]
       | Eff Cow (x,k) -> handler @@ k (3*x)
       | Eff Choose ((x,y),k) -> handler (k x) @ handler (k y)
     in handler))
   (fun res ->                          (* outer handler *)
     let rec handler = function 
       | Done -> [get_result res]
       | Eff Choose ((x,y),k) -> handler (k x) @ handler (k y)
     in handler)
;;
(*
val test4 : (int * int * int) list list =
  [[(1, 10, 9); (1, 20, 9)]; [(2, 10, 9); (2, 20, 9)]]
*)

(* Eff code: more complex nested handling

let test5 =
  let p = new nondeterminism in
  handle
    let a = p#choose (1, 2) in
    handle
      let b = p#choose (10, 20) in
      let c = p#cow 3 in
        (a, b, c)
    with
    | val v -> [v]
    | p#cow x k -> k (3 * x)
    | p#choose (x,y) k -> let z = p#choose (1000 * y, 100 * x) in k z
  with
  | val v -> [v]
  | p#choose (x,y) k -> k x @ k y
;;
*)

let test5 =
  let p = new_prompt () in
  handle_it p
  (fun () ->
    let a = choose p (1,2) in
    handle_it p (fun () -> 
      let b = choose p (10,20) in
      let c = cow p 3 in
     (a,b,c))
   (fun res -> (* inner handler *)
     let rec handler = function
       | Done -> [get_result res]
       | Eff Cow (x,k) -> handler @@ k (3*x)
       | Eff Choose ((x,y),k) -> 
           let z = choose p (1000 * y, 100 * x) in handler (k z)
     in handler))
   (fun res ->                          (* outer handler *)
     let rec handler = function 
       | Done -> [get_result res]
       | Eff Choose ((x,y),k) -> handler (k x) @ handler (k y)
     in handler)
;;
(*
val test5 : (int * int * int) list list =
  [[(1, 20000, 9)]; [(1, 1000, 9)]; [(2, 20000, 9)]; [(2, 1000, 9)]]
*)

(* Dynamic creation of effect instances *)

(* From pervasives.eff: dynamic effect creation for state

type 'a ref = effect
  operation lookup: unit -> 'a
  operation update: 'a -> unit
end

let state r x = handler
  | val y -> (fun _ -> y)
  | r#lookup () k -> (fun s -> k s s)
  | r#update s' k -> (fun _ -> k () s')
  | finally f -> f x;;

let ref x =
  new ref @ x with
    operation lookup _ @ x -> (x, x)
    operation update y @ _ -> ((), y)
  end

let (!) r = r#lookup ()
let (:=) r v = r#update v
let incr r = r#update (r#lookup () + 1)
let decr r = r#update (r#lookup () - 1)
*)

type 'a state =
  | Get of unit * ('a -> 'a state result)
  | Put of 'a  * (unit -> 'a state result)

let get p arg = shift0 p (fun k -> Eff (Get (arg,k)))
let put p arg = shift0 p (fun k -> Eff (Put (arg,k)))

(* Generic handler of state requests *)
let rec handler_ref s res = function
  | Done     -> get_result res
  | Eff Get (_,k) -> handler_ref s res @@ k s
  | Eff Put (s,k) -> handler_ref s res @@ k ()

(* We can use the state effect as usual *)
let tests1 = 
  let a = new_prompt () in              (* instantiate *)
  handle_it a 
  (fun () -> 
    let u = get a () in
    let v = get a () in
    put a (v + 30);
    let w = get a () in
    (u,v,w))
   (handler_ref 10)
;;

(*
val tests1 : int * int * int = (10, 10, 40)
*)

(* Now, we instatiate the state effect dynamically *)
(* We can create arbitrarily many instances of arbitrary types *)

let tests2 = 
  let pnew = new_prompt () in
  push_prompt pnew (fun () ->
    let newref s0 = 
      shift pnew (fun k ->
        let refname = new_prompt () in
        handle_it refname (fun () -> k refname) (handler_ref s0))
  in
    let a = newref 10 in      (* Dynamic instance of state effect *)
    let u = get a () in
    let v = get a () in
    put a (v + 30);
    let b = newref "a" in     (* Dynamic instance of a different type *)
    let w = get a () in
    (u,v,w,get b ())
 )
;;
(*
val tests2 : int * int * int * string = (10, 10, 40, "a")
*)

(* Wrap the handler h around the computation *)

type 'eff dyn_instance =
  | New of 'eff hr * ('eff result prompt -> 'eff dyn_instance result)
 and
  'eff hr = {h: 'w. 'w result_value -> 'eff result -> 'w}


let new_instance p arg = shift0 p (fun k -> Eff (New (arg,k)))

let rec new_handler res = function
  | Done -> get_result res
  | Eff New ({h=h},k) ->
      Printf.eprintf "new\n";
      let new_instance_p = new_prompt () in
      handle_it new_instance_p (fun () -> new_handler res @@ k new_instance_p) h

let tests21 = 
  let pnew = new_prompt () in
  handle_it pnew 
  (fun () ->
    let newref s0 = new_instance pnew ({h = fun res -> handler_ref s0 res}) in
    let a = newref 10 in      (* Dynamic instance of state effect *)
    let u = get a () in
    let v = get a () in
    put a (v + 30);
    let b = newref 40 in
    let w = get a () in
    (u,v,w,get b ())
 )
 new_handler
;;


(* It works, but without polymorphism. Now, try polymorphism *)

type 'eff handler_t = {h: 'w. 'w result_value -> 'eff result -> 'w}
type dyn_instance =
    New : 'eff handler_t * ('eff result prompt -> dyn_instance result) ->
     dyn_instance

let new_instance p arg = shift0 p (fun k -> Eff (New (arg,k)))

let rec new_handler res = function
  | Done -> get_result res
  | Eff New ({h=h},k) ->
      Printf.eprintf "new\n";
      let new_instance_p = new_prompt () in
      handle_it new_instance_p (fun () -> new_handler res @@ k new_instance_p) h

let tests22 = 
  let pnew = new_prompt () in
  handle_it pnew 
  (fun () ->
    let newref s0 = new_instance pnew ({h = fun res -> handler_ref s0 res}) in
    let a = newref 10 in      (* Dynamic instance of state effect *)
    let u = get a () in
    let v = get a () in
    put a (v + 30);
    let b = newref "a" in
    let w = get a () in
    (u,v,w,get b ())
 )
 new_handler
;;

