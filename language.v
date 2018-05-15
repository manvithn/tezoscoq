From Coq Require Import String List.
Import ListNotations.
From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp.algebra
  Require Import ssralg ssrnum ssrint.
Set Implicit Arguments.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Types.

Inductive instr_type :=
| Arrow : list type -> list type -> instr_type

with type :=
| t_int
| t_bool : type
| t_pair : type -> type -> type
| t_or : type -> type -> type
| t_option : type -> type
| t_list : type -> type
| t_string : type
| t_map : type -> type -> type
| t_signature : type
| t_key : type
| t_tez : type
| t_contract : type -> type -> type
| t_unit : type
| t_quotation : instr_type -> type
| t_timestamp.

Definition stack_type := list type.
End Types.

Infix "-->" := Arrow (at level 75).

Section DataAndInstr.

Inductive tez := Tez : nat -> tez.
(* TODO: change *)
Definition timestamp := nat.

(* Definition Map (A : Type) (B : Type) := list (prod A B). *)
(* Definition empty_map A B : Map A B := @nil (prod A B). *)

(* Definition get A B (m : Map A B) (x : A) := None. *)

(* please kill me now *)
(* Axiom Map : Type. *)
(* Axiom empty_map : Map. *)
(* Axiom get : forall A B (m : Map A B) (x : A), option A. *)
(* Axiom put : forall A B (m : Map A B) (x : A), Map A B. *)

(* for now, many items are commented as we are trying to get the
architecture right and don't want to get clogged with very similar
cases over and over. As we get more confident that we got things
right, we will uncomment new elements *)

Section Map.
(* purely mathematical view of functional maps *)

Definition myMap A B := seq (prod A B).

Definition empty_map {A} {B} := @nil (prod A B).

Definition put {A B} (key : A) (value : B) (m : myMap A B) : myMap A B :=
(key,value)::m.

Definition contains {A} {B}
(eq : A -> A -> bool) (k : A) (* (v : B) *) (m : myMap A B) :=
  has (fun kv => eq kv.1 k) m.

Definition remove {A} {B}
  (eq : A -> A -> bool) (k : A) (v : B) (m : myMap A B) :=
  (filter (fun kv => negb (eq kv.1 k)) m).

Definition checked_put {A} {B} eq (k : A) (v : B) m :=
  (k,v)::(remove eq k v m).

Definition get {A} {B}
(eq : A -> A -> bool) (k : A) (defk : A) (defv : B) (m : myMap A B) :=
  let index := find (fun kv => eq kv.1 k) m in
  if (index < size m)%N then
    Some (nth defv (map snd m) index) else None.

End Map.

Section String_missing.

Definition eq_string (s1 s2 : string) : bool.
  case: (string_dec s1 s2) => H12; [exact: true|exact: false].
Defined.

End String_missing.

Section Hash.
(* Hash function (sha256, abstracted away here) *)

Inductive hashT : Type :=
| hash : string -> hashT.

End Hash.


Section String_or_hash.

Inductive string_or_hash :=
| Sstring : string -> string_or_hash
| Shash : hashT -> string_or_hash.

Definition eq_string_or_hash s1 s2 :=
  match s1,s2 with
    | Sstring s1, Sstring s2 => eq_string s1 s2
    | Shash (hash s1),Shash (hash s2) => eq_string s1 s2
    (* if we had a concrete hashing function we would not do this of course: *)
    | _,_ => false
  end.

Definition to_string s1 : string :=
  match s1 with
    | Sstring s1 => s1
    | Shash (hash s1) => "<hash of "++s1++">"
  end.

End String_or_hash.

Local Coercion to_string : string_or_hash >-> string.

Section Signature.

Inductive key : Type :=
  K : string -> key.

Inductive sig : Type :=
  Sign : key -> string_or_hash -> sig.

Definition check_signature (k : key) (s : sig) (text : string_or_hash) :=
  match k, s with
    | K key, Sign (K key') raw => eq_string key key' && eq_string_or_hash raw text
  end.

End Signature.

(* for now we adopt a deliberately simple model where there are only
explicit accounts and implicit ones and their handles are natural integers incremented by the blockchain (see blockchain.v) *)
(* type for contract handles *)
(* Inductive handle := *)
(* | originated : hashT -> handle *)
(* | implicit : hashT -> handle. *)

Definition handle := nat.

Inductive tagged_data :=
| Int : int -> tagged_data
| Unit
| DBool : bool -> tagged_data
| DString : string_or_hash -> tagged_data
| DKey : key -> tagged_data
| DSignature : sig -> tagged_data
| Timestamp : timestamp -> tagged_data
| DTez : tez -> tagged_data
| DPair : tagged_data -> tagged_data -> tagged_data
| DOr : (sum tagged_data tagged_data) -> tagged_data
| DMap : myMap tagged_data tagged_data -> tagged_data
| DLambda : instr -> tagged_data
| DOption : (option tagged_data) -> tagged_data
| DContract : handle -> tagged_data
| DList : list tagged_data -> tagged_data
with
instr : Type :=
| Seq : instr -> instr -> instr
| Done : instr
| Nop : instr
| Fail : instr
| If : instr -> instr -> instr
| Loop : instr -> instr
| Dip : instr -> instr
| Drop : instr
| Dup : instr
| Swap : instr
| Push : tagged_data -> instr
| Pair : instr
| Eq : instr
| Neq : instr
| Lt : instr
| Le : instr
| Gt : instr
| Ge : instr
| Not : instr
| And : instr
| Or : instr
| Mul : instr
| Add : instr
| Sub : instr
| Lambda : instr -> instr
| Compare : instr
| Car : instr
| Cdr : instr
| ISome : instr
| INone : instr
| ILeft : instr
| IRight : instr
| If_none : instr -> instr -> instr
| If_some : instr -> instr -> instr
| If_left : instr -> instr -> instr
| If_right : instr -> instr -> instr
| Hash : instr
| Get : instr
| Check_signature : instr
| Map_reduce : instr
| Balance : instr
| Transfer_tokens : instr
| Exec : instr
| Create_contract : instr
.

Fixpoint serialize (t : tagged_data) : string :=
  match t with
    | Int n => "placeholder for integers"
    | DString s => s
    | Unit => "()"
    | DBool true => "true"
    | DBool false => "false"
    | DKey (K s) => "key: "++ s
    | DSignature (Sign (K key) text) => "sign("++key++","++text++")"
    | Timestamp t => "<timestamp>"
    | DTez t => "<some amount in tezos>"
    | DPair a b => "("++(serialize a)++", "++(serialize b)++")"
    | DOr o => match o with inl a => "Left " ++ (serialize a) | inr b => "Right " ++ (serialize b) end
    | DMap m => "<map>"
    | DLambda l => "<lambda>"
    | DOption o => match o with Some o => "Some " ++ (serialize o) | None => "None" end
    | DContract handle => "<Contract : <handle> >"
    | DList l => "<TODO: encoding of lists>"
  end.

Definition get_raw_hash (x : tagged_data) :=
  (Shash (hash (serialize x))).

Definition get_hash (x : tagged_data) : tagged_data :=
  DString (get_raw_hash x).

(* partial equality, TODO: finish *)
Fixpoint eq_td x y :=
  match x,y with
    | Int m, Int n => m == n
    | DString (Sstring s1), DString (Sstring s2) => (* dirty *) eq_string s1 s2
    | DString (Shash (hash x1)),DString (Shash (hash x2)) => eq_string x1 x2
    | _, _ => false
  end.

(* | Signature <signature constant> *)
(* | Key <key constant> *)
(* | Left <tagged data> <type> *)
(* | Right <type> <tagged data> *)
(* | Or <type> <type> <untagged data> *)
(* | Ref <tagged data> *)
(* | Ref <type> <untagged data> *)
(* | Some <tagged data> *)
(* | Some <type> <untagged data> *)
(* | None <type> *)
(* | Option <type> <untagged data> *)
(* | Pair <type> <type> <untagged data> <untagged data> *)
(* | List <type> <untagged data> ... *)
(* | Set <comparable type> <untagged data> ... *)
(* | Map <comparable type> <type> (Item <untagged data> <untagged data>) ... *)
(* | Contract <type> <type> <contract constant> *)
(* | Lambda <type> <type> { <instruction> ... } *)

Definition is_comparable (d : tagged_data) : bool :=
  match d with
    | Int _ | DBool _ | DTez _ | Timestamp _ => true
    | _ => false
  end.

Definition is_bool d :=
  match d with
    | DBool _ => true
    | _ => false
  end.

Definition is_int i :=
  match i with
    | Int _ => true
    | _ => false
  end.

Definition is_pair x :=
  match x with
    | DPair _ _ => true
    | _ => false
  end.

Definition is_or x := 
  match x with
    | DOr (inl _) => true
    | DOr (inr _) => true
    | _ => false
  end.

Definition is_option x := 
  match x with
    | DOption (Some _) => true
    | DOption None => true
    | _ => false
  end.

Definition stack := list tagged_data.

End DataAndInstr.

(* Notations don't survive the end of section:
   that's why they are here *)

(* Notations for data *)
Notation "x %tz " := (DTez (Tez x)) (at level 80, right associativity).
Notation "s %s" := ((Sstring s)) (at level 80, right associativity).
Notation "s %ds" := (DString (Sstring s)) (at level 80, right associativity).
Notation "k %k" := ((K k)) (at level 80, right associativity).
Notation "k %dk" := (DKey (K k)) (at level 80, right associativity).
(* Notation "#signof< k , sig , text >" := (Sign k sig text) (at level 79, right associativity). *) (* does not work *)
Notation "#hashof< h >" := ((Shash (hash h))) (at level 80, right associativity).
(* TODO: find better notation, with smarter precedence for pairs *)
Notation "'{' x ',' y '}'" := (DPair x y) (at level 80, right associativity).
Notation "#left< x >" := (DOr (inl x)) (at level 80, right associativity).
Notation "#right< x >" := (DOr (inr x)) (at level 80, right associativity).
Notation "#some< x >" := (DOption (Some x)) (at level 80, right associativity).
Notation "#none" := (DOption None) (at level 80, right associativity).

(* Notations for instructions *)

Notation "c1 ';;' c2" := (Seq c1 c2) (at level 80, right associativity).
Notation "'DONE'" := (Done).
Notation "'NOP'" := (Nop).
(* TODO: check if IF or IFB *)
Notation "'IFB' '{{' bt '}}' '{{' bf '}}'" := (If bt bf) (at level 80, right associativity).
Notation "'LOOP' '{{' body '}}'" := (Loop body) (at level 80, right associativity).
Notation "'DIP' '{{' code '}}'" := (Dip code) (at level 80, right associativity).
Notation "'DROP'" := (Drop).
Notation "'DUP'" := (Dup).
Notation "'SWAP'" := (Swap).
Notation "'PUSH' x" := (Push x) (at level 35).
Notation "'UNIT'" := (Push Unit).
Notation "'PAIR'" := (Pair).
Notation "'EQ'" := (Eq).
Notation "'NEQ'" := (Neq).
Notation "'LT'" := (Lt).
Notation "'LE'" := (Le).
Notation "'GT'" := (Gt).
Notation "'GE'" := (Ge).
Notation "'NOT'" := (Not).
Notation "'AND'" := (And).
Notation "'OR'" := (Or).
Notation "'MUL'" := (Mul).
Notation "'ADD'" := (Add).
Notation "'SUB'" := (Sub).
Notation "'LAMBDA' '{{' body '}}'" := (Lambda body) (at level 80, right associativity).
Notation "'COMPARE'" := (Compare).
Notation "'IFCMPLT' '{{' bt '}}' '{{' bf '}}'" := (Compare;; Lt;; If bt bf) (at level 80, right associativity).
Notation "'IFCMPLE' '{{' bt '}}' '{{' bf '}}'" := (Compare;; Le;; If bt bf) (at level 80, right associativity).
Notation "'IFCMPGT' '{{' bt '}}' '{{' bf '}}'" := (Compare;; Gt;; If bt bf) (at level 80, right associativity).
Notation "'IFCMPGE' '{{' bt '}}' '{{' bf '}}'" := (Compare;; Ge;; If bt bf) (at level 80, right associativity).
Notation "'CDR'" := (Cdr).
Notation "'CAR'" := (Car).
Notation "'CAAR'" := (CAR;; CAR).
Notation "'CADR'" := (CAR;; CDR).
Notation "'CDAR'" := (CDR;; CAR).
Notation "'CDDR'" := (CDR;; CDR).
Notation "'SOME'" := (ISome).
Notation "'NONE'" := (INone).
Notation "'LEFT'" := (ILeft).
Notation "'RIGHT'" := (IRight).
Notation "'IF_NONE' '{{' bt '}}' '{{' bf '}}'" := (If_none bf bt) (at level 80, right associativity).
Notation "'IF_SOME' '{{' bt '}}' '{{' bf '}}'" := (If_some bt bf) (at level 80, right associativity).
Notation "'IF_LEFT' '{{' bt '}}' '{{' bf '}}'" := (If_left bt bf) (at level 80, right associativity).
Notation "'IF_RIGHT' '{{' bt '}}' '{{' bf '}}'" := (If_right bt bf) (at level 80, right associativity).
Notation "'HASH'" := (Hash).
Notation "'GET'" := (Get).
Notation "'FAIL'" := (Fail).
Notation "'CHECK_SIGNATURE'" := (Check_signature).
Notation "'MAP_REDUCE'" := (Map_reduce).
Notation "'BALANCE'" := (Balance).
Notation "'TRANSFER_TOKENS'" := (Transfer_tokens).
Notation "'EXEC'" := (Exec).
Notation "'GET'" := (Get).

(* More DI...IPs. *)
Notation "'DIIP' '{{' code '}}'" := (Dip (Dip code)) (at level 80, right associativity).
Notation "'DIIIP' '{{' code '}}'" := (Dip (Dip (Dip code))) (at level 80, right associativity).

(* More DU...UPs. *)

Fixpoint Dup_rec (n : nat) :=
  match n with
    | O => Done
    | 1 => DUP
    | n.+1 => DIP {{ Dup_rec n }} ;; SWAP
  end.

(* Expecting the initial argument already on the stack. *)
Fixpoint Reduce_rec (lambda : instr) (m : myMap tagged_data tagged_data) : instr :=
  match m with
    | [] => Done
    | kv :: m =>  PUSH (DPair kv.1 kv.2) ;; PAIR ;; PUSH (DLambda lambda) ;;
        SWAP ;; EXEC ;; Reduce_rec lambda m
  end.

(*
Fixpoint Reduce_rec (lambda : instr) (m : myMap tagged_data tagged_data) (x : tagged_data) : option (prod instr stack) :=
  match m with
    | [] => Some(Done,[x])
    | kv::m => Some(PUSH (DLambda lambda);; PUSH (DPair (DPair kv.1 kv.2) x);; EXEC,nil)
  end.
*)
(* Fixpoint Reduce_rec (lambda : instr) (m : myMap tagged_data tagged_data) := *)
(* match m with *)
(*   | [] => Done *)
(*   | kv::m => PUSH kv.2;; lambda;; (Reduce_rec lambda m) end *)
(* . *)

Notation "'DUPn' n" := (Dup_rec n) (at level 80).
Notation "'DUUUUUUP'" := (Dup_rec 6) (at level 80).

(* TODO: have a general notation for 'some code between accolades' *)
(* Notation "'IF_SOME' '{{' '}}' '{{' bf '}}'" := (If_some NOP bf) (at level 80, right associativity). *)

(* Section TypingJudgements. *)   (* TODO: Notations won't survive the end of the section. Can we do anything about this? *)

(** Composition relation between instruction types.
    It's meant to be used for typing the `Seq` instruction. *)
Reserved Notation "IT1 '<o>' IT2 '===' IT3" (at level 70).
Inductive instr_type_composition : instr_type -> instr_type -> instr_type -> Prop :=
| IT_comp_nil1 : forall Sa Sc Sd,
    (** When 1st instruction doesn't produce output,
        the input stack must have all the elements
        for 1st _and_ 2nd instructions beforehand *)
    (Sa --> []) <o> (Sc --> Sd) === (Sa ++ Sc --> Sd)
| IT_comp_nil2 : forall Sa Sb Sd,
    (** When 2nd instruction doesn't consume input,
        it's output gets added to the output of 1st instruction *)
    (Sa --> Sb) <o> ([] --> Sd) === (Sa --> Sd ++ Sb)
| IT_comp_cons : forall Sa Sb Sc Sd Sx Sy t,
    (Sa --> Sb) <o> (Sc --> Sd) === (Sx --> Sy) ->
    (** When 1st instruction produces a value of type `t`,
        2nd instruction must consume a value of the same type *)
    (Sa --> t :: Sb) <o> (t :: Sc --> Sd) === (Sx --> Sy)
where "IT1 '<o>' IT2 '===' IT3" := (instr_type_composition IT1 IT2 IT3).

(* TODO: write instr_type_composition as a function
Fixpoint compose_instr_type (t1 t2 : instr_type) : instr_type := ...
*)

Hint Constructors instr_type_composition.

Reserved Notation "i ':i:' IT" (at level 40).
Reserved Notation "d ':d:' DT" (at level 40).
Inductive has_instr_type : instr -> instr_type -> Prop :=
| IT_Seq : forall i1 i2 Sa Sb Sc Sd Sx Sy,
    i1 :i: (Sa --> Sb) ->
    i2 :i: (Sc --> Sd) ->
    (Sa --> Sb) <o> (Sc --> Sd) === (Sx --> Sy) ->
    (i1 ;; i2) :i: (Sx --> Sy)
| IT_Done :
    DONE :i: ([] --> [])
| IT_Nop : forall S,
(* Should we generalize this pattern? What about DONE? *)
    NOP :i: (S --> S)
| IT_Drop : forall t,
    DROP :i: ([ t ] --> [])
| IT_Dup : forall t,
    DUP :i: ([ t ] --> [ t ; t ])
| IT_Swap : forall t1 t2,
    SWAP :i: ([ t1 ; t2 ] --> [ t2 ; t1 ])
| IT_Push : forall v t,
    v :d: t ->
    PUSH v :i: ([] --> [ t ])
| IT_Pair : forall t1 t2,
    PAIR :i: ([t1 ; t2] --> [ t_pair t1 t2 ])
| IT_Dip : forall t code Sa Sb,
    code :i: (Sa --> Sb) ->
    (DIP {{ code }}) :i: (t :: Sa --> t :: Sb)
| IT_If : forall Sa Sb bt bf,
    bt :i: (Sa --> Sb) ->
    bf :i: (Sa --> Sb) ->
    (IFB {{ bt }} {{ bf }}) :i: (t_bool :: Sa --> Sb)
| IT_Loop : forall S body,
    body :i: (S --> t_bool :: S) ->
    (LOOP {{ body }}) :i: (t_bool :: S --> S)
| IT_Eq :
    EQ :i: ([ t_int ] --> [ t_bool ])
| IT_Neq :
    NEQ :i: ([ t_int ] --> [ t_bool ])
| IT_Mul :
    MUL :i: ([ t_int ; t_int ] --> [ t_int ])
| IT_Sub :
    SUB :i: ([ t_int ; t_int ] --> [ t_int ])
| IT_Lt :
    Lt :i: ([ t_int ] --> [ t_bool ])
| IT_Le :
    Le :i: ([ t_int ] --> [ t_bool ])
| IT_Gt :
    Gt :i: ([ t_int ] --> [ t_bool ])
| IT_Ge :
    Ge :i: ([ t_int ] --> [ t_bool ])
| IT_Not :
    Not :i: ([ t_bool ] --> [ t_bool ])
| IT_And :
    And :i: ([ t_bool ; t_bool ] --> [ t_bool ])
| IT_Or :
    Or :i: ([ t_bool ; t_bool ] --> [ t_bool ])
| IT_Add :
    Add :i: ([ t_int ; t_int ] --> [ t_int ])
| IT_Lambda : forall b Sb,
    b :i: Sb ->
    Lambda b :i: ([] --> [ t_quotation Sb ])
| IT_Compare : forall t,
    Compare :i: ([ t ; t ] --> [ t_int ])
| IT_Car : forall t1 t2,
    Car :i: ([ t_pair t1 t2 ] --> [ t1 ])
| IT_Cdr : forall t1 t2,
    Cdr :i: ([ t_pair t1 t2 ] --> [ t2 ])
| IT_ISome : forall t,
    ISome :i: ([ t ] --> [ t_option t ])
| IT_INone : forall t,
    INone :i: ([] --> [ t_option t ])
| IT_ILeft : forall l r,
    ILeft :i: ([ l ] --> [ t_or l r ])
| IT_IRight :  forall l r,
    IRight :i: ([ r ] --> [ t_or l r ])
| IT_If_None : forall a b S bt bf,
    bt :i: (S --> b :: S) ->
    bf :i: (a :: S --> b :: S) ->
    If_none bt bf :i: (t_option a :: S --> b :: S)
| IT_If_Some : forall a b S bt bf,
    bt :i: (a :: S --> b :: S) ->
    bf :i: (S --> b :: S) ->
    If_some bt bf :i: (t_option a :: S --> b :: S)
| IT_If_Left : forall a b c S bt bf,
    bt :i: (a :: S --> c :: S) ->
    bf :i: (b :: S --> c :: S) ->
    If_left bt bf :i: (t_or a b :: S --> c :: S)
| IT_If_Right : forall a b c S bt bf,
    bt :i: (b :: S --> c :: S) ->
    bf :i: (a :: S --> c :: S) ->
    If_right bt bf :i: (t_or a b :: S --> c :: S)
| IT_Hash : forall t,
    Hash :i: ([ t ] --> [ t_string ])
| IT_Get : forall tk tv,
    Get :i: ([ tk ; t_map tk tv ] --> [ t_option tv ])
| IT_Fail : forall Sa Sb,
    Fail :i: (Sa --> Sb)
| IT_Check_signature :
    Check_signature :i: ([ t_key; t_pair t_signature t_string ] --> [ t_bool ])
| IT_Map_reduce : forall tk tv t,
    Map_reduce :i: ([ t_quotation ([t_pair (t_pair tk tv) t ] --> [ t ]) ; t_map tk tv ; t ] --> [ t ])
| IT_Balance :
    Balance :i: ([] --> [ t_tez ])
(* TODO: is that correct? Anything to ensure on g? *)
| IT_Transfer_tokens : forall p r g,
    Transfer_tokens :i: ([ p ; t_tez ; t_contract p r ; g ] --> [ r ; g ] )
where "i ':i:' IT" := (has_instr_type i IT)

with has_data_type : tagged_data -> type -> Type :=
| T_Bool : forall b, DBool b :d: t_bool
| T_Int : forall z, Int z :d: t_int
| T_Unit : Unit :d: t_unit
| T_Pair : forall a b ta tb, a :d: ta -> b :d: tb -> DPair a b :d: t_pair ta tb
| T_OrLeft : forall o tl tr, o :d: tl -> DOr (inl o) :d: t_or tl tr
| T_OrRight : forall o tl tr, o :d: tr -> DOr (inr o) :d: t_or tl tr
| T_Tez : forall t, DTez t :d: t_tez
| T_Key : forall k, DKey (K k) :d: t_key
| T_OptionSome : forall o t, o :d: t -> DOption (Some o) :d: t_option t
| T_OptionNone : forall t, DOption None :d: t_option t
| T_map : forall m dfk dfv ta tb, dfk :d: ta -> dfv :d: tb -> (forall i, let kv := nth (dfk,dfv) m i in DPair kv.1 kv.2 :d: t_pair ta tb) -> DMap m :d: t_map ta tb
| T_string : forall s, DString s :d: t_string
| T_list : forall l A, DList l :d: t_list A
| T_timestamp : forall n, Timestamp n :d: t_timestamp
| T_signature : forall k s, DSignature (Sign k s) :d: t_signature
where "d ':d:' DT" := (has_data_type d DT).

Hint Constructors has_instr_type.
Hint Constructors has_data_type.
Hint Resolve cats0.
(* instr_type_composition is going to produce a lot of subterms
   of the form `xs ++ [::]`, that's why the following hint might
   come in handy *)
Hint Extern 4 ((_ = _)) => repeat rewrite cats0.

(* a test for the `repeat rewrite cats0` hint *)
Goal forall (T : Type) (xs : seq T), ((xs ++ []) ++ []) ++ [] = xs.
  auto. Qed.

(* The `instr_type_composition` relation is
   a partial binary function *)
Lemma instr_type_composition_functional : forall STa STb ST1 ST2,
  STa <o> STb === ST1 ->
  STa <o> STb === ST2 ->
  ST1 = ST2.
Proof.
move => STa STb ST1 ST2 H1 H2.
elim: H1 H2.
- move => Sa Sc Sd Hc2. by inversion Hc2; auto.
- move => Sa Sb Sd Hc2. by inversion Hc2; auto.
- move => Sa Sb Sc Sd Sx Sy t Hc1 IH Hc2.
  by inversion Hc2; subst; intuition.
Qed.

(*
   The following tactic should've been implemented just with
   `econstructor` all the way down.
   For some reason Coq can't unify arguments when it comes to
   applying IT_comp_nil1 or IT_comp_nil2 using `apply` or `econstructor`.
   `refine (<constructor_name> _ _ _)` works, but this is obviously a crutch.

TODO: find a way to implement this more elegantly.

For example, then typechecking

  (DROP ;; DROP) :i: ([t1 ; t2] --> []).

When it comes to the last `econstructor` application we have the following two terms to unify:
?X   --> [] // ?Y   --> ?Z \\ ?X ++ ?Y  --> ?Z
with
[?A] --> [] // [?B] --> [] \\ [t1; t2] --> []

This is obviously can be done:
?X = [?A]  |  ?Y = [?B]  |   ?Z = []
And
[?A] ++ [?B] = [t1; t2]
?A = t1
?B = t2
 *)

Ltac typecheck_program :=
  tryif econstructor
    then typecheck_program
    else refine (IT_comp_nil1 _ _ _) || refine (IT_comp_nil2 _ _ _).

(*End TypingJudgements.*)

(* provides a default value for each type *)
Fixpoint default (t : type) : tagged_data :=
  match t with
    | t_int => Int 0
    | t_unit => Unit
    | t_bool => DBool true
    | t_pair a b => DPair (default a) (default b)
    | t_or a b => DOr (inl (default a))
    | t_string => DString (Sstring "")
    | t_option ta => (DOption (Some(default ta)))
    | t_list ta => DList [default ta]
    | t_map ta tb => DMap ([(default ta, default tb)])
    | t_signature => DSignature (Sign (K "default key") (Sstring ""))
    | t_key => DKey (K "default key")
    | t_tez => DTez (Tez 0)
    | t_contract a b => DContract 0%nat(* (DROP;;PUSH (default b)) *)
    | t_quotation a => Unit (* missing datatype *)
    | t_timestamp => Timestamp 0%nat
  end.


Definition well_typed_map ta tb m := (forall i, let kv := nth (default ta,default tb) m i in DPair kv.1 kv.2 :d: t_pair ta tb).

Lemma type_default (t : type) : default t :d: t.
Proof.
elim: t => //= .
- by move => ta Ha tb Hb // ; constructor.
- by move => t Ht;constructor.
- by move => t Ht;constructor.
- move => t H t' Ht'. econstructor.
    exact: H.
    exact: Ht'.
    case => [|i] //= ; constructor => //= .
    by rewrite nth_nil.
    by rewrite nth_nil.
- admit. (* FIXME *)
- admit. (* FIXME *)
Admitted.

Lemma typed_well_typed_map ta tb m : DMap m :d: t_map ta tb -> well_typed_map ta tb m.
Proof.
move => H; inversion H.
move => i.
case Hi : (size m <= i)%N.
  by rewrite nth_default //= ; constructor; exact: type_default.
rewrite (set_nth_default (dfk,dfv)) //.
by rewrite ltnNge Hi.
Qed.
