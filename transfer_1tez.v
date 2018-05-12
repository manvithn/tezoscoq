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

Definition transfer_1tez_prog :=
    (* Extract account for the recipient of the funds *)
    CAR ;;
    (* Push a value of the storage type below the contract *)
    DIP {{ UNIT }} ;;
    (* Give the person a tez *)
    PUSH (1 %tz) ;;
    (* Push the contract's argument type *)
    UNIT ;;
    (* Run the transfer *)
    TRANSFER_TOKENS ;;
    (* Cleanup and put the return values *)
    PAIR.

Theorem transfer_1tez_prog_type :
  transfer_1tez_prog :i: ([ t_pair (t_contract t_unit t_unit) t_unit ] --> [ t_pair t_unit t_unit ]).
Proof. by typecheck_program. Qed.

(*
Inductive var := B : nat -> var .

Definition f x :=
  match x with
  | B n => if n > (5%:Z) then None else Some (Int n)
  end.

Lemma success x:
  forall y,
  f x = Some y -> y = Int 1.
Proof.
  intros.
  unfold f in H.
  destruct x.
  discriminate.
  destruct n.
  inversion H.
  trivial.
Qed.
*)

Lemma transfer_success_returns_unit ch rh b0:
  forall r b1,
  transfer_tokens Unit (Tez 1) ch rh Unit b0 = Some (r, b1) ->
  r = Unit.
Proof.
  intros R B H.
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
      destruct n.
      - simpl in H.
        discriminate. 
      - simpl in H.
        inversion H.
        trivial. 
  all: discriminate.
Qed. 

(*
  ch, rh : handles of contracts, ch = current handle, rh = handle of input contract i.e. receiver
  state : (i * s * b) option
  i : instructions
  s : stack
  b : blockchain (mapping from handles to contract_reprs)
 *)
Theorem transfer_1 ch rh b0:
  forall r b1,
  transfer_tokens Unit (Tez 1) ch rh Unit b0 = Some (r, b1) ->
  evaluates
    ch
    (Some (transfer_1tez_prog, [:: { DContract rh, Unit }], b0))
    (Some (Done, [:: { Unit, Unit }], b1)).
Proof.
  intros R B P.
  do 9 apply: evaluates_onestep => /= .
  cut (R = Unit).
  intros RisUnit.
  rewrite RisUnit in P.
  apply: evaluates_onestep => /=.
  rewrite P => /=.
  do 2 apply: evaluates_onestep => /=.
  exact: evaluates_self => /=.
  apply (@transfer_success_returns_unit ch rh b0 R B).
  trivial.
Qed.

Theorem transfer_fail ch rh b0:
  transfer_tokens Unit (Tez 1) ch rh Unit b0 = None ->
  evaluates
    ch
    (Some (transfer_1tez_prog, [:: { DContract rh, Unit }], b0))
    None.
Proof.
  intros P.
  do 9 apply: evaluates_onestep => /= .
  apply: evaluates_onestep => /=.
  rewrite P => /=.
  exact: evaluates_self => /=.
Qed.
