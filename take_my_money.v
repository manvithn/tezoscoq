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

Definition take_my_money_program :=
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

Theorem typing_take_my_money :
  take_my_money_program :i: ([ t_pair (t_contract t_unit t_unit) t_unit ] --> [ t_pair t_unit t_unit ]).
Proof. by typecheck_program. Qed.

(*
  h, hinp : handles of contracts, h = current handle, hinp = handle of input contract
  state : (i * s * m) option
  i : instructions
  s : stack
  b : blockchain (mapping from handles to contract_reprs)
 *)
Theorem balance_reduces_by_1 ch rh b0:
  forall r b1,
  transfer_tokens Unit (Tez 1) ch rh Unit b0 = Some (r, b1) ->
  evaluates ch (Some (take_my_money_program, [:: { DContract rh, Unit } ], b0)) (Some (Done, [:: { Unit, Unit } ], b1)).
Proof.
  intros R B P.
Qed.