From Coq Require Import String List.
Import ListNotations.
From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp.algebra
  Require Import ssralg ssrnum ssrint.
Set Implicit Arguments.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

From Tezos
  Require Import language blockchain semantics.

Definition auction_prog :=
    (* Compare the parameter timestamp with the storage timestamp; fail if auction has ended *)
    DUP ;; DUP ;; CAR ;; CAR ;; DIP {{ CDR ;; CAR }} ;; IFCMPGE {{ FAIL }} {{ NOP }} ;;
    (* Compare the parameter amount with the storage amount; fail if amount is lower *)
    DUP ;; DUP ;; CAR ;; CDR ;; CAR ;; DIP {{ CDR ;; CDR ;; CAR }} ;; SWAP ;; IFCMPGE {{ FAIL }} {{ NOP }} ;;
    (* Get the storage amount and contract *)
    DUP ;; DUP ;; CDR ;; CDR ;; CAR ;; DIP {{ CDR ;; CDR ;; CDR }} ;;
    (* Update storage *)
    DIIP {{ DUP ;; CDAR ;; DIP {{ CADR }} ;; PAIR }} ;;
    (* Run the transfer *)
    UNIT ;; TRANSFER_TOKENS ;;
    (* Cleanup and put the return values *)
    PAIR.

Theorem auction_prog_type :
  auction_prog :i: (
    [ t_pair
            (t_pair t_timestamp (t_pair t_tez (t_contract t_unit t_unit)))
            (t_pair t_timestamp (t_pair t_tez (t_contract t_unit t_unit))) ] -->
    [ t_pair
            t_unit
            (t_pair t_timestamp (t_pair t_tez (t_contract t_unit t_unit))) ]).
Proof. by typecheck_program. Qed.  

(* 
Inductive var := B : nat -> var.

Definition f a b :=
  if (a < b)%N then None else Some Unit.

Lemma success a b :
  forall y,
  f a b = Some y -> y = Unit.
Proof.
  intros.
  unfold f in H.
  set cond := ((a < b)%N) in H.
  destruct cond.
  - discriminate.
  - inversion H.
    trivial.
Qed.
*)

(*
Inductive var := A | B.

Definition g a :=
  if (a == 0)%N then A else B.

Definition f a :=
  match g a with
  | A => None
  | B => Some Unit
  end.

Lemma success :
  forall y,
  f y = Some Unit -> g y = B.
Proof.
  intros.
  unfold f in H.
  destruct (g y).
  discriminate.
  trivial.
Qed.
*)

Lemma auction_success_returns_unit ch rh b0 :
  forall a s r b1,
  transfer_tokens Unit (Tez a) ch rh s b0 = Some (r, b1) ->
  r = Unit.
Proof.
  intros A S R B H.
  unfold transfer_tokens in H.
  set getrh := (get_contract rh b0) in H.
  set getch := (get_contract ch b0) in H.
  destruct getrh as [ c0 | ].
  - destruct c0 as [p0 rstorage].
    destruct p0 as [rcontract rbalance].
    destruct getch as [ c1 | ].
    - destruct c1 as [p1 sstorage].
      destruct p1 as [scontract sbalance].
      destruct sbalance.
      destruct rbalance.
      set cond := ((A <= n)%N) in H.
      destruct cond.
      - inversion H.
        trivial.
  all: discriminate.
Qed. 

Theorem auction_bid_higher_correct_refund ch b0 :
  forall t0 a0 h0 t1 a1 h1 r b1,
  let (amt0, amt1) := (a0%tz, a1%tz) in
  let (tstamp0, tstamp1) := (Timestamp t0, Timestamp t1) in
  let (contract0, contract1) := (DContract h0, DContract h1) in
  let parameter := { tstamp1 , { amt1 , contract1 } } in
  let storage0 := { tstamp0 , { amt0 , contract0 } } in
  let storage1 := { tstamp0 , { amt1 , contract1 } } in
  (t0 > t1)%N ->
  (a0 < a1)%N ->
  transfer_tokens Unit (Tez a0) ch h0 storage1 b0 = Some (r, b1) ->
  evaluates
    ch
    (Some (auction_prog, [:: { parameter , storage0 } ], b0))
    (Some (Done, [:: { Unit, storage1 }], b1)).
Proof.
  intros t0 a0 h0 t1 a1 h1 r b1 T A P.
  cut (r = Unit).
  intros RisUnit.
  rewrite RisUnit in P.
  do 14 apply: evaluates_onestep => /= .
  rewrite T.
  cut ((t1 == t0 = false)%N).
  intro TT.
  rewrite TT.
  do 26 apply: evaluates_onestep => /= .
  rewrite A.
  cut ((a0 == a1 = false)%N).
  intro AA.
  rewrite AA.
  do 40 apply: evaluates_onestep => /= .
  apply evaluates_onestep => /=.
  rewrite P => /=.
  do 2 apply: evaluates_onestep => /=.
  exact: evaluates_self => /=.
  cut ((a0 < a1 -> a0 == a1 = false)%N).
  auto.
  apply (@ltn_eqF a0 a1).
  cut ((t1 < t0 -> t1 == t0 = false)%N).
  auto.
  apply (@ltn_eqF t1 t0).
  set s := ({ Timestamp t0, { a1 %tz, DContract h1} }) in P.
  apply (@auction_success_returns_unit ch h0 b0 a0 s r b1).
  trivial.
Qed.

Theorem auction_bid_higher_exists ch b0 :
  forall t0 a0 h0 t1 a1 h1 r b1,
  let (amt0, amt1) := (a0%tz, a1%tz) in
  let (tstamp0, tstamp1) := (Timestamp t0, Timestamp t1) in
  let (contract0, contract1) := (DContract h0, DContract h1) in
  let parameter := { tstamp1 , { amt1 , contract1 } } in
  let storage0 := { tstamp0 , { amt0 , contract0 } } in
  let storage1 := { tstamp0 , { amt1 , contract1 } } in
  (t0 > t1)%N ->
  (a0 < a1)%N ->
  transfer_tokens Unit (Tez a0) ch h0 storage1 b0 = Some (r, b1) ->
  exists con bal s,
  Some (con, Tez bal, s) = get_contract ch b0 /\
  Some (con, Tez (bal - a0), s) = get_contract ch b1.
Proof.
  intros t0 a0 h0 t1 a1 h1 r b1 T A P.
  unfold transfer_tokens in P.
  set getrh := (get_contract h0 b0) in P.
  destruct getrh as [ c0 | ].
  - destruct c0 as [p0 rstorage].
    destruct p0 as [rcontract rbalance].
    destruct (get_contract ch b0) as [ c1 | ].
    - destruct c1 as [p1 sstorage].
      destruct p1 as [scontract sbalance].
      destruct sbalance as [ sbalance ].
      destruct rbalance as [ rbalance ].
      apply ex_intro with scontract.
      apply ex_intro with sbalance.
      apply ex_intro with sstorage.
      split.
      - trivial.
      - destruct ((a0 <= sbalance)%N).
        inversion P.
        set conrep0 := (scontract, Tez (sbalance - a0), sstorage).
        set conrep1 := (rcontract, Tez (rbalance + a0), rstorage).
        set b01 := (checked_put eqkey ch conrep0 b0).
        cut (Some conrep0 = get_contract ch b01).
        apply put_does_not_change.
      - apply put_then_get.
  all: discriminate.
Qed.

Theorem auction_bid_lower ch b0 :
  forall t0 a0 h0 t1 a1 h1,

  let (amt0, amt1) := (a0%tz, a1%tz) in
  let (tstamp0, tstamp1) := (Timestamp t0, Timestamp t1) in
  let (contract0, contract1) := (DContract h0, DContract h1) in
  let parameter := { tstamp1 , { amt1 , contract1 } } in
  let storage0 := { tstamp0 , { amt0 , contract0 } } in
  let storage1 := { tstamp0 , { amt1 , contract1 } } in
  (t0 > t1)%N ->
  (a0 >= a1)%N ->
  evaluates
    ch
    (Some (auction_prog, [:: { parameter , storage0 } ], b0))
    None.
Proof.
  intros t0 a0 h0 t1 a1 h1 T A.
  do 14 apply: evaluates_onestep => /= .
  rewrite T.
  cut ((t1 == t0 = false)%N).
  intro TT.
  rewrite TT.
  do 26 apply: evaluates_onestep => /= .
  set cond1 := ((a0 == a1)%N).
  destruct cond1.
  - do 5 apply: evaluates_onestep => /= .
    exact: evaluates_self => /=.
  - cut ((a0 < a1 = false)%N).
    intro AA.
    rewrite AA.
    do 5 apply: evaluates_onestep => /=.
    exact: evaluates_self => /=.
  apply (@negbTE (a0 < a1)%N).
  rewrite <- (@leqNgt a1 a0).
  apply A.
  cut ((t1 < t0 -> t1 == t0 = false)%N).
  auto.
  apply (@ltn_eqF t1 t0).
Qed.

Theorem auction_timeout ch b0 :
  forall t0 a0 h0 t1 a1 h1,

  let (amt0, amt1) := (a0%tz, a1%tz) in
  let (tstamp0, tstamp1) := (Timestamp t0, Timestamp t1) in
  let (contract0, contract1) := (DContract h0, DContract h1) in
  let parameter := { tstamp1 , { amt1 , contract1 } } in
  let storage0 := { tstamp0 , { amt0 , contract0 } } in
  let storage1 := { tstamp0 , { amt1 , contract1 } } in
  (t0 <= t1)%N ->
  evaluates
    ch
    (Some (auction_prog, [:: { parameter , storage0 } ], b0))
    None.
Proof.
  intros t0 a0 h0 t1 a1 h1 T.
  do 14 apply: evaluates_onestep => /= .
  set cond1 := ((t1 == t0)%N).
  destruct cond1.
  - do 5 apply: evaluates_onestep => /= .
    exact: evaluates_self => /=.
  - cut ((t1 < t0 = false)%N).
    intro TT.
    rewrite TT.
    do 5 apply: evaluates_onestep => /=.
    exact: evaluates_self => /=.
  apply (@negbTE (t1 < t0)%N).
  rewrite <- (@leqNgt t0 t1).
  apply T.
Qed.
