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

effect Select : 'a list -> 'a

let rec filter p = function
  | [] -> []
  | x :: xs ->
    if p x then (x :: filter p xs) else filter p xs

let rec forall p = function
  | [] -> true
  | x :: xs -> if p x then forall p xs else false

let no_attack (x,y) (x',y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let available x qs l =
  filter (fun y -> forall (no_attack (x,y)) qs) l

let backtracking_queens n =
  try
    let l = ref [] in
    for i = n downto 1 do
      l := i::!l;
    done;
    let rec place x qs =
      if x = n+1 then Some qs else
        let y = perform @@ Select (available x qs !l) in
        place (x+1) ((x, y) :: qs)
    in place 1 []
  with
  | effect (Select lst) k ->
      let rec loop = function
        | [] -> None
        | x::xs ->
            match continue (Obj.clone_continuation k) x with
            | None -> loop xs
            | Some x -> Some x
      in loop lst

(******************************************************************************)

let available number_of_queens x qs =
  let rec loop possible y =
    if y < 1 then possible else
    if List.for_all (no_attack (x, y)) qs then loop (y :: possible) (y - 1) else loop possible (y - 1)
  in
  loop [] number_of_queens

exception Fail

let queens_one_fail number_of_queens =

  let rec place x qs =
    if x > number_of_queens then qs else
      let rec loop = function
        | [] -> raise Fail
        | y :: ys ->
          begin try place (x + 1) ((x, y) :: qs) with
            | Fail -> loop ys
          end
      in
      loop (available number_of_queens x qs)
  in

  match place 1 [] with
  | _ -> ()
  | exception Fail -> ()

(******************************************************************************)

let queens_one_option number_of_queens =

  let rec place x qs =
    if x > number_of_queens then Some qs else
      let rec loop = function
        | [] -> None
        | y :: ys ->
          begin match place (x + 1) ((x, y) :: qs) with
            | Some qs -> Some qs
            | None -> loop ys
          end
      in
      loop (available number_of_queens x qs)
  in

  ignore (place 1 [])

(******************************************************************************)

module Generated = struct

  type effect_symbol = string

  type ('eff_arg, 'eff_res) effect_type = effect_symbol

  type 'a computation =
    | Value : 'a -> 'a computation
    | Call : ('eff_arg, 'eff_res) effect_type * 'eff_arg * ('eff_res -> 'a computation) -> 'a computation

  type ('a, 'b) value_clause = 'a -> 'b computation
  type ('a, 'b) finally_clause = 'a -> 'b computation

  type 'a effect_clauses =
    | Nil : 'a effect_clauses
    | Cons : ('eff_arg, 'eff_res) effect_type * ('eff_arg -> ('eff_res -> 'a computation) -> 'a computation) * 'a effect_clauses -> 'a effect_clauses

  type ('a, 'b, 'c) handler = {
    value_clause: ('a, 'b) value_clause;
    finally_clause: ('b, 'c) finally_clause;
    effect_clauses: 'b effect_clauses;
  }

  let rec find_case : 'eff_arg 'eff_res. ('eff_arg, 'eff_res) effect_type -> 'a effect_clauses -> ('eff_arg -> ('eff_res -> 'a computation) -> 'a computation) =
    fun eff eff_clauses ->
      match eff_clauses with
      | Nil ->
        (fun x k -> Call (eff, x, k))
      | Cons (eff', case, eff_clauses) ->
        if eff = eff' then Obj.magic case else find_case eff eff_clauses

  let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
    match c with
    | Value x -> f x
    | Call (eff, arg, k) -> Call (eff, arg, fun y -> k y >> f)

  let rec handle (h : ('a, 'b, 'c) handler) (c : 'a computation) : 'c computation =
    let rec handler = function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
      let f = find_case eff h.effect_clauses in
      f arg (fun y -> handler (k y))
    in
    handler c >> h.finally_clause

  let value (x : 'a) : 'a computation = Value x

  let call (eff : ('a, 'b) effect_type) (arg : 'a) (cont : 'b -> 'c computation) : 'c computation =
    Call (eff, arg, cont)

  let effect_type eff = fun arg -> call eff arg value

  let run = function
    | Value x -> x
    | Call (eff, _, _) -> failwith ("Uncaught effect_type " ^ eff)

  let (=) = fun x -> value (fun y -> value (Pervasives.(=) x y))
  let (<) = fun x -> value (fun y -> value (Pervasives.(<) x y))

  let (~-) = fun x -> value (Pervasives.(~-) x)
  let (+) = fun x -> value (fun y -> value (Pervasives.(+) x y))
  let ( * ) = fun x -> value (fun y -> value (Pervasives.( * ) x y))
  let (-) = fun x -> value (fun y -> value (Pervasives.(-) x y))
  let (mod) = fun x -> value (fun y -> value (Pervasives.(mod) x y))
  let (~-.) = fun x -> value (Pervasives.(~-.) x)
  let (+.) = fun x -> value (fun y -> value (Pervasives.(+.) x y))
  let ( *. ) = fun x -> value (fun y -> value (Pervasives.( *. ) x y))
  let (-.) = fun x -> value (fun y -> value (Pervasives.(-.) x y))
  let (/.) = fun x -> value (fun y -> value (Pervasives.(/.) x y))
  let (/) = fun x -> value (fun y -> value (Pervasives.(/) x y))
  let ( ** ) =
    let rec pow a = Pervasives.(function
    | 0 -> 1
    | 1 -> a
    | n ->
      let b = pow a (n / 2) in
      b * b * (if n mod 2 = 0 then 1 else a)) in
    fun x -> value (fun y -> value (pow x y))

  let float_of_int = fun x -> value (Pervasives.float_of_int x)
  let (^) = fun x -> value (fun y -> value (Pervasives.(^) x y))
  let string_length = fun x -> value (String.length x)
  let to_string = fun _ -> failwith "Not implemented"

  ;;
  let _var_1 : 't1 -> ('t1 -> ( bool) computation) computation = ( = );;
  let _var_2 : 't2 -> ('t2 -> ( bool) computation) computation = ( < );;
  let effect_Print : ( string,  unit) effect_type = "effect_Print";;
  let effect_Read : ( unit,  string) effect_type = "effect_Read";;
  let effect_Raise : ( unit, 'empty) effect_type = "effect_Raise";;
  let _var_3 = (fun _var_4 ->  (match _var_4 with _ -> assert false));;
  let effect_DivisionByZero : ( unit, 'empty) effect_type = "effect_DivisionByZero";;
  let effect_InvalidArgument : ( string, 'empty) effect_type = "effect_InvalidArgument";;
  let effect_Failure : ( string, 'empty) effect_type = "effect_Failure";;
  let _var_5 = (fun _var_6 ->
    call effect_Failure _var_6 (fun _var_4 ->  _var_3 _var_4));;
  let effect_AssertionFault : ( unit, 'empty) effect_type = "effect_AssertionFault";;
  let _var_8 = (fun _var_9 ->
    (match _var_9 with | true ->
                          value ()
                        | false ->
                          call effect_AssertionFault () (fun _var_9 ->  _var_3
                                                          _var_9)));;
  let _var_11 :  int -> ( int) computation = ( ~- );;
  let _var_12 :  int -> ( int -> ( int) computation) computation = ( + );;
  let _var_13 :  int -> ( int -> ( int) computation) computation = ( * );;
  let _var_14 :  int -> ( int -> ( int) computation) computation = ( - );;
  let _var_15 :  int -> ( int -> ( int) computation) computation = ( mod );;
  let _var_16 = (fun _var_17 ->  value (fun _var_18 ->
    (match _var_18 with | 0 ->
                            call effect_DivisionByZero () (fun _var_14 ->
                                                              _var_3
                                                          _var_14)
                        | _var_20 ->
                            value (Pervasives.(mod)
                        _var_17
                        _var_20))));;
  let _var_22 :  float -> ( float) computation = ( ~-. );;
  let _var_23 :  float -> ( float -> ( float) computation) computation = ( +. );;
  let _var_24 :  float -> ( float -> ( float) computation) computation = ( *. );;
  let _var_25 :  float -> ( float -> ( float) computation) computation = ( -. );;
  let _var_26 :  float -> ( float -> ( float) computation) computation = ( /. );;
  let _var_27 :  int -> ( int -> ( int) computation) computation = ( / );;
  let _var_28 :  int -> ( int -> ( int) computation) computation = ( ** );;
  let _var_29 = (fun _var_30 ->  value (fun _var_31 ->
    (match _var_31 with | 0 ->
                            call effect_DivisionByZero () (fun _var_21 ->
                                                              _var_3
                                                          _var_21)
                        | _var_33 ->
                            value (Pervasives.(/)
                        _var_30
                        _var_33))));;
  let _var_35 :  int -> ( float) computation = ( float_of_int );;
  let _var_36 :  string -> ( string -> ( string) computation) computation = ( ^ );;
  let _var_37 :  string -> ( int) computation = ( string_length );;
  let _var_38 : 't3 -> ( string) computation = ( to_string );;
  type ('t4) option = None|Some of 't4;;let rec _var_39 = fun _var_40 ->
    value (fun _var_41 ->
    (match _var_41 with | [] ->
                            value None
                        | ((::) ((_var_42, _var_43), _var_44)) ->
                            (match Pervasives.(=)
                        _var_40
                        _var_42 with | true ->
                                        value (Some _var_43)
                                      | false ->
                                        (_var_39 _var_40) >>
                                        fun _var_47 ->  _var_47 _var_44)));;
  let _var_48 = (fun _var_49 ->
    (match _var_49 with | true ->
                            value false
                        | false ->
                            value true));;let _var_50 = (fun _var_51 ->
    value (fun _var_52 ->  value (Pervasives.(<) _var_52 _var_51)));;
  let _var_54 = (fun _var_55 ->  value (fun _var_56 ->
    let _var_57 = Pervasives.(<) _var_55 _var_56 in
  let _var_59 = Pervasives.(=) _var_55 _var_56 in
  (match _var_57 with | true ->
                        value true
                      | false ->
                        value _var_59)));;let _var_61 = (fun _var_62 ->
    value (fun _var_63 ->
    (_var_54 _var_63) >> fun _var_64 ->  _var_64 _var_62));;
  let _var_65 = (fun _var_66 ->  value (fun _var_67 ->  _var_48 (Pervasives.(=)
  _var_66 _var_67)));;let _var_70 = (fun _var_71 ->  value (fun _var_72 ->
    _var_48 (Pervasives.(=) _var_71 _var_72)));;
  let rec _var_75 = fun _var_76 ->  value (fun _var_77 ->
    (_var_50 _var_76) >>
    fun _var_79 ->
        (_var_79 _var_77) >>
        fun _var_78 ->
          (match _var_78 with | true ->
                                  value []
                              | false ->
                                  (_var_75 (Pervasives.(+) _var_76 1)) >>
                                  fun _var_82 ->
                                    (_var_82 _var_77) >>
                                    fun _var_81 ->
                                        value ((::) (_var_76, _var_81))));;
  let rec _var_85 = fun _var_86 ->  value (fun _var_87 ->
    (match _var_87 with | [] ->
                            value []
                        | ((::) (_var_88, _var_89)) ->
                            (_var_86 _var_88) >>
                            fun _var_90 ->
                              (_var_85 _var_86) >>
                              fun _var_92 ->
                                  (_var_92 _var_89) >>
                                  fun _var_91 ->
                                    value ((::) (_var_90, _var_91))));;
  let _var_93 = (fun _ ->  value ());;let _var_94 = (fun ((::) (_var_95, _)) ->
    value _var_95);;let _var_96 = (fun ((::) (_, _var_97)) ->
    value _var_97);;let _var_98 = (fun _var_99 ->  value (fun _var_100 ->
    (_var_75 0) >>
    fun _var_102 ->
        (_var_102 _var_100) >>
        fun _var_101 ->
          (_var_85 _var_99) >> fun _var_103 ->  _var_103 _var_101));;
  let rec _var_104 = fun _var_105 ->  value (fun _var_106 ->
    value (fun _var_107 ->
    (match _var_107 with | [] ->
                            value _var_106
                          | ((::) (_var_108, _var_109)) ->
                            (_var_105 _var_106) >>
                            fun _var_111 ->
                                (_var_111 _var_108) >>
                                fun _var_110 ->
                                  (_var_104 _var_105) >>
                                  fun _var_113 ->
                                      (_var_113 _var_110) >>
                                      fun _var_112 ->  _var_112 _var_109)));;
  let rec _var_114 = fun _var_115 ->  value (fun _var_116 ->
    value (fun _var_117 ->
    (match _var_116 with | [] ->
                            value _var_117
                          | ((::) (_var_118, _var_119)) ->
                            (_var_114 _var_115) >>
                            fun _var_122 ->
                                (_var_122 _var_119) >>
                                fun _var_121 ->
                                  (_var_121 _var_117) >>
                                  fun _var_120 ->
                                      (_var_115 _var_118) >>
                                      fun _var_123 ->  _var_123 _var_120)));;
  let rec _var_124 = fun _var_125 ->  value (fun _var_126 ->
    (match _var_126 with | [] ->
                            value ()
                          | ((::) (_var_127, _var_128)) ->
                            (_var_125 _var_127) >>
                            fun _ ->
                                (_var_124 _var_125) >>
                                fun _var_129 ->  _var_129 _var_128));;
  let rec _var_130 = fun _var_131 ->  value (fun _var_132 ->
    (match _var_132 with | [] ->
                            value true
                          | ((::) (_var_133, _var_134)) ->
                            (_var_131 _var_133) >>
                            fun _var_135 ->
                                (match _var_135 with | true ->
                                                        (_var_130 _var_131) >>
                                                        fun _var_136 ->
                                                          _var_136
                                                        _var_134
                                                    | false ->
                                                        value false)));;
  let rec _var_137 = fun _var_138 ->  value (fun _var_139 ->
    (match _var_139 with | [] ->
                            value false
                          | ((::) (_var_140, _var_141)) ->
                            (_var_138 _var_140) >>
                            fun _var_142 ->
                                (match _var_142 with | true ->
                                                        value true
                                                    | false ->
                                                        (_var_137 _var_138) >>
                                                        fun _var_143 ->
                                                          _var_143
                                                        _var_141)));;
  let _var_144 = (fun _var_145 ->  _var_137 (fun _var_146 ->
    value (Pervasives.(=) _var_145 _var_146)));;
  let rec _var_148 = fun _var_149 ->  value (fun _var_150 ->
    (match _var_150 with | [] ->
                            value []
                          | ((::) (_var_151, _var_152)) ->
                            (_var_149 _var_151) >>
                            fun _var_153 ->
                                (match _var_153 with | true ->
                                                        (_var_148 _var_149) >>
                                                        fun _var_155 ->
                                                          (_var_155 _var_152)
                                                          >>
                                                          fun _var_154 ->
                                                              value ((::) (
                                                          _var_151, _var_154))
                                                    | false ->
                                                        (_var_148 _var_149) >>
                                                        fun _var_156 ->
                                                          _var_156
                                                        _var_152)));;
  let _var_157 = (fun _var_158 ->  value (fun _var_159 ->
    (_var_148 (fun _var_161 ->
        (_var_144 _var_161) >>
        fun _var_163 ->
          (_var_163 _var_159) >> fun _var_162 ->  _var_48 _var_162)) >>
    fun _var_160 ->  _var_160 _var_158));;let _var_164 = (fun _var_165 ->
    value (fun _var_166 ->
    (_var_148 (fun _var_168 ->
        (_var_144 _var_168) >> fun _var_169 ->  _var_169 _var_166)) >>
    fun _var_167 ->  _var_167 _var_165));;let rec _var_170 = fun _var_171 ->
    value (fun _var_172 ->
    (match (_var_171, _var_172) with | ([], []) ->
                                        value []
                                      | (((::) (_var_173, _var_174)),
                                        ((::) (_var_175, _var_176))) ->
                                        (_var_170 _var_174) >>
                                        fun _var_178 ->
                                            (_var_178 _var_176) >>
                                            fun _var_177 ->
                                              value ((::) ((_var_173, _var_175),
                                                            _var_177))
                                      | (_, _) ->
                                        call effect_InvalidArgument "zip: length mismatch" (
                                      fun _var_44 ->  _var_3 _var_44)));;
  let _var_180 = (fun _var_181 ->
    let rec _var_182 = fun _var_183 ->  value (fun _var_184 ->
                (match _var_184 with | [] ->
                                        value _var_183
                                    | ((::) (_var_185, _var_186)) ->
                                        (_var_182 ((::) (_var_185, _var_183)))
                                        >> fun _var_187 ->  _var_187 _var_186)) in
  (_var_182 []) >> fun _var_188 ->  _var_188 _var_181);;
  let rec _var_189 = fun _var_190 ->  value (fun _var_191 ->
    (match _var_190 with | [] ->
                            value _var_191
                          | ((::) (_var_192, _var_193)) ->
                            (_var_189 _var_193) >>
                            fun _var_195 ->
                                (_var_195 _var_191) >>
                                fun _var_194 ->
                                  value ((::) (_var_192, _var_194))));;
  let rec _var_196 = fun _var_197 ->
    (match _var_197 with | [] ->
                            value 0
                          | ((::) (_var_198, _var_199)) ->
                            (_var_196 _var_199) >>
                            fun _var_201 ->  value (Pervasives.(+) _var_201 1));;
  let _var_202 = (fun _var_203 ->
    (match _var_203 with | [] ->
                            call effect_InvalidArgument "head: empty list" (
                          fun _var_51 ->  _var_3 _var_51)
                          | ((::) (_var_205, _)) ->
                            value _var_205));;
  let rec _var_206 = fun _var_207 ->
    (match _var_207 with | [] ->
                            call effect_InvalidArgument "tail: empty list" (
                          fun _var_56 ->  _var_3 _var_56)
                          | ((::) (_var_209, _var_210)) ->
                            value _var_210);;let _var_211 = (fun _var_212 ->
    (match Pervasives.(<) _var_212
  0 with | true ->
            value (Pervasives.(~-)
        _var_212)
        | false ->
            value _var_212));;let _var_215 = (fun _var_216 ->
    value (fun _var_217 ->  (match Pervasives.(<) _var_216
  _var_217 with | true ->
                  value _var_216
                | false ->
                  value _var_217)));;let _var_220 = (fun _var_221 ->
    value (fun _var_222 ->  (match Pervasives.(<) _var_221
  _var_222 with | true ->
                  value _var_222
                | false ->
                  value _var_221)));;let rec _var_225 = fun _var_226 ->
    value (fun _var_227 ->
    (match _var_227 with | 0 ->
                            value _var_226
                          | _ ->
                            (_var_225 _var_227) >>
                            fun _var_228 ->
                                (_var_16 _var_226) >>
                                fun _var_230 ->
                                  (_var_230 _var_227) >>
                                  fun _var_229 ->  _var_228 _var_229));;
  let rec _var_231 = fun _var_232 ->  value (fun _var_233 ->
    (_var_225 _var_232) >>
    fun _var_235 ->
        (_var_235 _var_233) >>
        fun _var_234 ->
          (_var_29 (Pervasives.( * ) _var_232 _var_233)) >>
          fun _var_236 ->  _var_236 _var_234);;let _var_239 = (fun _var_240 ->
    (_var_16 _var_240) >>
    fun _var_243 ->
        (_var_243 2) >> fun _var_242 ->  value (Pervasives.(=) _var_242 1));;
  let _var_244 = (fun _var_245 ->
    (_var_16 _var_245) >>
    fun _var_248 ->
        (_var_248 2) >> fun _var_247 ->  value (Pervasives.(=) _var_247 0));;
  let _var_249 = (fun _var_250 ->  value _var_250);;
  let _var_251 = (fun _var_252 ->  value (fun _var_253 ->
    value (fun _var_254 ->
    (_var_253 _var_254) >> fun _var_255 ->  _var_252 _var_255)));;
  let _var_256 = (fun (_var_257, _) ->  value _var_257);;
  let _var_258 = (fun (_, _var_259) ->  value _var_259);;
  let _var_260 = (fun _var_261 ->
    (_var_38 _var_261) >>
    fun _var_262 ->
        call effect_Print _var_262 (fun _var_73 ->  value _var_73));;
  let _var_263 = (fun _var_264 ->
    call effect_Print _var_264 (fun _var_76 ->  value _var_76));;
  let _var_265 = (fun _var_266 ->
    (_var_38 _var_266) >>
    fun _var_267 ->
        call effect_Print _var_267 (fun _var_83 ->  let _ = _var_83 in
                                    call effect_Print "\n" (fun _var_79 ->
                                                              value _var_79)));;
  let effect_Lookup : ( unit,  int) effect_type = "effect_Lookup";;
  let effect_Update : ( int,  unit) effect_type = "effect_Update";;
  let _var_268 = (fun _var_269 ->  value (fun _var_270 ->
    value { value_clause = (fun _var_278 ->  value (fun _ ->  value _var_278));
            finally_clause = (fun _var_277 ->  _var_277 _var_270);
            effect_clauses = Cons ((effect_Lookup), (fun () _var_274 -> value (fun _var_275 ->
              (_var_274 _var_275) >> fun _var_276 ->  _var_276 _var_275)), (Cons ((effect_Update), (fun _var_271 _var_272 -> value (fun _ ->
              (_var_272 ()) >> fun _var_273 ->  _var_273 _var_271)), (Nil)))) }));;
  let effect_Decide : ( unit,  bool) effect_type = "effect_Decide";;
  let effect_Fail : ( unit, 'empty) effect_type = "effect_Fail";;
  let rec _var_279 = fun _var_280 ->
    (match _var_280 with | [] ->
                            call effect_Fail () (fun _var_88 ->  _var_3
                                                  _var_88)
                          | ((::) (_var_282, _var_283)) ->
                            call effect_Decide () (fun _var_93 ->
                                                      (match _var_93 with
                                                    | true ->
                                                      value _var_282
                                                    | false ->
                                                      _var_279
                                                    _var_283)));;
  let _var_285 = { value_clause = (fun _var_290 ->  value _var_290);
                  finally_clause = (fun _var_289 ->  value _var_289);
                  effect_clauses = Cons ((effect_Decide), (fun () _var_286 -> handle {
                  value_clause = (fun _var_288 ->  value _var_288);
                  finally_clause = (fun _var_287 ->  value _var_287);
                  effect_clauses = Cons ((effect_Fail), (fun () _ -> _var_286
                  false), (Nil)) } (_var_286 true)), (Nil)) };;
  let _var_291 = { value_clause = (fun _var_297 ->  value ((::) (_var_297, [])));
                  finally_clause = (fun _var_296 ->  value _var_296);
                  effect_clauses = Cons ((effect_Decide), (fun () _var_292 ->
                  (_var_292 true) >>
                  fun _var_294 ->
                    (_var_189 _var_294) >>
                    fun _var_293 ->
                        (_var_292 false) >> fun _var_295 ->  _var_293 _var_295), (Cons ((effect_Fail), (fun _ _ -> value []), (Nil)))) };;
  let _var_298 = (fun (_var_299, _var_300) ->
    value (fun (_var_301, _var_302) ->
    (_var_65 _var_299) >>
    fun _var_304 ->
        (_var_304 _var_301) >>
        fun _var_303 ->
          (match _var_303 with | true ->
                                  (_var_65 _var_300) >>
                                  fun _var_306 ->
                                      (_var_306 _var_302) >>
                                      fun _var_305 ->
                                        (match _var_305 with | true ->
                                                                (_var_211
                                                                (Pervasives.(-)
                                                                _var_299
                                                                _var_301)) >>
                                                                fun _var_308 ->
                                                                    (_var_65
                                                                    _var_308)
                                                                    >>
                                                                    fun _var_307 ->

                                                                    (_var_211
                                                                    (Pervasives.(-)
                                                                    _var_300
                                                                    _var_302))
                                                                    >>
                                                                    fun _var_311 ->
                                                                      _var_307
                                                                    _var_311
                                                              | false ->
                                                                value false)
                                | false ->
                                  value false)));;
  let _var_314 = (fun _var_315 ->  value (fun _var_316 ->
    value (fun _var_317 ->
    let rec _var_318 = fun _var_319 ->  value (fun _var_320 ->
                (match Pervasives.(<) _var_320
            1 with | true ->
                      value _var_319
                    | false ->
                      (_var_298 (_var_316, _var_320)) >>
                      fun _var_325 ->
                          (_var_130 _var_325) >>
                          fun _var_324 ->
                            (_var_324 _var_317) >>
                            fun _var_323 ->
                                (match _var_323 with | true ->
                                                        (_var_318
                                                        ((::) (_var_320,
                                                              _var_319))) >>
                                                        fun _var_326 ->
                                                          _var_326
                                                        (Pervasives.(-)
                                                        _var_320 1)
                                                    | false ->
                                                        (_var_318 _var_319) >>
                                                        fun _var_329 ->
                                                          _var_329
                                                        (Pervasives.(-)
                                                        _var_320 1)))) in
  (_var_318 []) >> fun _var_332 ->  _var_332 _var_315)));;
  let _var_333 = (fun _var_334 ->
    let rec _var_335 = fun _var_336 ->  value (fun _var_337 ->
                (_var_50 _var_336) >>
                fun _var_339 ->
                  (_var_339 _var_334) >>
                  fun _var_338 ->
                      (match _var_338 with | true ->
                                              value _var_337
                                          | false ->
                                              (_var_314 _var_334) >>
                                              fun _var_343 ->
                                                (_var_343 _var_336) >>
                                                fun _var_342 ->
                                                    (_var_342 _var_337) >>
                                                    fun _var_341 ->
                                                      (_var_279 _var_341) >>
                                                      fun _var_340 ->
                                                          (_var_335
                                                          (Pervasives.(+)
                                                          _var_336 1)) >>
                                                          fun _var_344 ->
                                                            _var_344
                                                          ((::) ((_var_336,
                                                                  _var_340),
                                                                _var_337)))) in
  (_var_335 1) >> fun _var_347 ->  _var_347 []);;
  let _var_348 = (fun _var_349 ->  handle _var_285 (_var_333 _var_349));;
  let _var_350 = (fun _var_351 ->  handle _var_291 (_var_333 _var_351))
  let run2 = _var_348
end

let main () =
  let n =
    if Array.length Sys.argv > 1
    then int_of_string Sys.argv.(1)
    else 8
  in
  let (m,sd) = Benchmark.benchmark 5 (fun () ->
    (*
    let Some l = backtracking_queens n in
    List.iter (fun (x,y) -> Printf.printf "(%d,%d) " x y) l;
    print_endline "") in *)
    ignore @@ backtracking_queens n) in
  Printf.printf "queens_ocaml_multicore: \t mean = %f, sd = %f\n%!" m sd;

  let (m,sd) = Benchmark.benchmark 5 (fun () -> queens_one_fail n) in
  Printf.printf "queens_one_fail: \t mean = %f, sd = %f\n%!" m sd;

  let (m,sd) = Benchmark.benchmark 5 (fun () -> queens_one_option n) in
  Printf.printf "queens_one_option: \t mean = %f, sd = %f\n%!" m sd;

  let (m,sd) = Benchmark.benchmark 5 (fun () ->
    (* let l = Generated.run @@ Generated.run2 n in
    List.iter (fun (x,y) -> Printf.printf "(%d,%d) " x y) l;
    print_endline "") in *)
    ignore @@ Generated.run @@ Generated.run2 n) in
  Printf.printf "eff(optimized): \t mean = %f, sd = %f\n%!" m sd

let () = main ()

