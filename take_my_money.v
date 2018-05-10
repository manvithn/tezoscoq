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

Example typing_take_my_money :
  take_my_money_program :i: ([ t_pair (t_contract t_unit t_unit) t_unit ] --> [ t_pair t_unit t_unit ]).
Proof. by typecheck_program. Qed.

Lemma 