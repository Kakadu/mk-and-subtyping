include struct
   open OCanren
   type ('name, 'terms) term = Term of 'name * 'terms

   let fmt_term fname fterms fmt (Term (s, xs)) =
     Format.fprintf fmt "('%a %a)" fname s fterms xs

   type ground = (string,               ground OCanren.Std.List.ground) term
   type logic  = (string OCanren.logic, logic  OCanren.Std.List.logic)  term OCanren.logic
   type tinj = (ground, logic) injected

   module F = OCanren.Fmap2(struct
      type  ('a, 'b) t = ('a,'b) term
      let fmap fa fb (Term (a,b)) = Term (fa a, fb b)
   end)

   let w name xs = inj @@ F.distrib @@ Term (name, xs)
   (* in [w name xs] xs is obliged to be a list of terms. Is it what is expected? *)

   let leaf name = w name (Std.List.nil ())

   let rec term_reify env t : logic =
      F.reify OCanren.reify (OCanren.Std.List.reify term_reify) env t
   let rec pp_term_logic fmt t =
      GT.fmt OCanren.logic
         (fmt_term (GT.fmt OCanren.logic (GT.fmt GT.string))
                  (GT.fmt Std.List.logic pp_term_logic))
         fmt t

end


(* ****** Relational stuff ******************** *)
let (!!) x = OCanren.(inj @@ lift x)

(*
(define contravariant-subtype (lambda (a b)
  (conde
    ( (is-reference b)      (subtype b a)       )
    ( (is-valuetype b) (== b a) )
)))
*)

include struct
  open OCanren
  open OCanren.Std

let ibox1 arg = w !!"iboxz" !<arg
let object3 = w !!"object3" (Std.List.nil())
let thing2  = w !!"thing2"  (Std.List.nil())

let rec contravariant_subtype a b =
  conde
    [ (is_reference b) &&& (subtype b a)
    ; (is_valuetype b) &&& (b ===  a)
    ]

(*
(define is-reference (lambda (a)
  (conde
    ((fresh (q)
       (== a `(ibox1 ,q)) ) )

    ( (== a 'object3) )
    ( (== a 'thing2) )
    ( (== a a) )
)))
*)
and is_reference a  =
  conde
    [ fresh (q)
        (a === ibox1 q)
    ; (a === object3)
    ; (a === thing2)
    ; success
    ]

(*
(define is-valuetype (lambda (a) fail ))
*)
and is_valuetype a = failure
(*
(define not-contravariant-subtype (lambda (a b)
  (conde
    ( (is-reference b) (not-subtype b a))
    ( (is-valuetype b) (=/= b a) )
)))
*)
and not_contravariant_subtype a b =
  conde
    [ (is_reference b) &&& (not_subtype b a)
    ; (is_valuetype b) &&& (b =/= a)
    ]
(*
(define not-subtype (lambda (t st)
  (conde
    ( (fresh (q)
	(== t `(ibox1 ,q))
	(== st 'thing2)
      ))
    ( (fresh (a b)
	(== t  `(ibox1 ,a))
	(== st `(ibox1 ,b))
	(not-contravariant-subtype a b)
	))
    ( (fresh (q)
        (== t  'object3)
	(== st `(ibox1 ,q))	) )
    ( (== t 'object3) (== st 'thing2) )
    ( (fresh (a)
        (not-subtype `(ibox1 (ibox1 thing2)) `(ibox1 ,a) )
	(== t  'thing2)
	(== st `(ibox1 ,a)) ))
)))
 *)
and not_subtype t st =
  conde
    [ fresh (q)
        (t === w !!"ibox1" q)
        (st === leaf !!"thing2")
    ; fresh (a b)
        (t === w !!"ibox1" !<a)
        (st === w !!"ibox1" !<b)
        (not_contravariant_subtype a b)
    ; fresh (q)
        (t === leaf !!"object3")
        (st === w !!"ibox1" q)
    ; (t === leaf !!"object3") &&& (st === leaf !!"thing2")
    ; fresh (a)
        (t === leaf !!"thing2")
        (st === w !!"ibox1" !<a)
        (not_subtype (w !!"ibox1" !<(w !!"ibox1" !<(leaf !!"thing2"))) (w !!"ibox1" !<a))
    ]
(*

(define subtype (lambda (t st)
  (conde
    ( (fresh (a)
        (== st 'object3)
        (== t `(ibox1 ,a)) ))
    ( (fresh (a b)
 	 (== t  `(ibox1 ,a))
 	 (== st `(ibox1 ,b))
	 (contravariant-subtype a b)    ))
    ( (== t 'object3) (== st t) )
    ( (fresh (a)
        (== t 'thing2)
        (== st `(ibox1 ,a))
        (subtype `(ibox1 (ibox1 thing2)) `(ibox1 ,a))  ))
    ( (== t 'thing2)  (== st 'object3) )
    ( (== t 'thing2)  (== st t) )
  )
))
*)
and subtype t st =
  conde
    [ fresh (a)
        (st === leaf !!"object3")
        (t  === w !!"ibox1" !<a)
    ; fresh (a b)
        (t === w !!"ibox1" !<a)
        (st === w !!"ibox1" !<b)
        (contravariant_subtype a b)
    ; (t === leaf !!"object3") &&& (st === t)
    ; fresh (a)
        (t === leaf !!"thing2")
        (st === w !!"ibox1" !<a)
        (subtype (w !!"ibox1" !<(w !!"ibox1" !<(leaf !!"thing2"))) (w !!"ibox1" !<a))
    ; (t === leaf !!"thing2") &&& (st === leaf !!"object3")
    ; (t === leaf !!"thing2") &&& (st === t)
    ]

end

let () =
  let my_reify r = r#reify term_reify in
  (let open OCanren  in
   let open OCanren.Std in
   run (succ one)
     (fun a b -> (a === b) &&& (not_subtype a (w !!"ibox1" !<(leaf !!"thing2"))) )
     (fun r r2 -> (my_reify r, my_reify r2) )
  )
  |> OCanren.Stream.take ~n:1
  |> List.iter (fun (l,m) -> Format.printf "(%a,%a)\n%!" pp_term_logic l pp_term_logic m)
