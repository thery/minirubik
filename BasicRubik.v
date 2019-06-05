Require Import ZArith.
Require Import List.

(*****************************************************************************)
(*                                                                           *)
(*               Some Properties of fold_left                                *)
(*                                                                           *)
(*****************************************************************************)

Lemma fold_left_cons (A B : Type) (f : A -> B -> A) 
                     (b : B) (l : list B) (i : A) :
  fold_left f (b :: l) i = fold_left f l (f i b).
Proof. trivial. Qed.

Lemma fold_right_cons (A B : Type) (f : B -> A -> A)
                      (b : B) (l : list B) (i : A) :
  fold_right f i (b :: l) =  f b (fold_right f i l).
Proof. trivial. Qed.

Lemma fold_left_comb (A B C D : Type) (f : B -> C -> D) (g : A -> D -> A)
                        (l1 : list C) (l2 : list B) (i : A) :
  fold_left (fun x y => 
      fold_left (fun x1 y1 => g x1 (f y y1)) l1 x) l2 i =
  fold_left g (fold_right (fun y x => (map (f y) l1)++x) nil l2) i .
Proof.
revert i; elim l2; simpl; auto; clear l2.
intros b l2 Hrec i.
rewrite Hrec.
rewrite fold_left_app.
apply f_equal2 with (f := fold_left g); auto.
generalize i; elim l1; simpl; auto; clear l1 Hrec.
Qed.


(*****************************************************************************)
(*                                                                           *)
(*                         Permutations                                      *)
(*                                                                           *)
(*****************************************************************************)


Inductive perm {A : Type} : list A -> list A -> Prop :=
  perm_id: forall l, perm l l
| perm_swap: forall a b l, 
    perm (a :: b :: l) (b :: a :: l)
| perm_skip: forall a l1 l2, 
    perm l1 l2 -> perm (a :: l1) (a :: l2)
| perm_trans: forall l1 l2 l3, 
    perm l1 l2 -> perm l2 l3 -> perm l1 l3.


(*****************************************************************************)
(*                                                                           *)
(*                         Uniqueness                                        *)
(*                                                                           *)
(*****************************************************************************)

Inductive unique {A: Type} : list A -> Prop :=
  uniqN: unique nil
| uniqC: forall (a : A) l, 
        unique l -> ~ In a l -> unique (a :: l).

Lemma unique_inv (A : Type) (a : A) l : unique (a:: l) -> unique l.
Proof. intro H; inversion H; auto. Qed.

Lemma unique_app (A: Type) (l1 l2: list A) : unique (l1 ++ l2) -> unique l1.
Proof.
elim l1; clear l1.
- intros; apply uniqN.
- intros a l1 Hrec H; inversion_clear H as [| xx yy Ha Hb].
  apply uniqC; auto with datatypes.
Qed.

Lemma unique_perm (A : Type) (l1 l2 : list A) : 
  perm l1 l2 -> unique l1 -> unique l2.
Proof.
intro H; elim H; clear l1 l2 H; auto.
- intros a b l H; inversion_clear H as [| xx yy Ha Hb].
  inversion_clear Ha as [| xx uu Ha1 Hb1].
  repeat apply uniqC; auto with datatypes.
  simpl; intros [H1 | H1]; subst; auto with datatypes.
- intros a l1 l2 H1 H2 H3.
  inversion_clear H3 as [| xx yy Ha Hb].
  apply uniqC; auto with datatypes.
  contradict Hb; generalize Hb; elim H1; clear l1 l2 H1 H2 Ha Hb;
    auto with datatypes.
  * simpl; intros a1 b1 l [H1 | [H1 | H1]]; auto.
  * simpl; intros a1 l1 l2 H Hrec [H1 | H1]; auto.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                   Equality test for positive                              *)
(*                                                                           *)
(*****************************************************************************)

Fixpoint positive_eq (p1 p2 : positive) {struct p1} : bool :=
  match p1, p2 with
    xH, xH => true
  | xO p3, xO p4 =>  positive_eq p3 p4
  | xI p3, xI p4 => positive_eq p3 p4
  | _, _ => false
  end.

Lemma positive_eq_correct p1 p2 :
  if positive_eq p1 p2 then p1 = p2 else p1 <> p2.
Proof.
revert p2; elim p1; [intros p3 Hrec | intros p3 Hrec|];
  intros p2; (case p2; [intros p4 | intros p4 |]); simpl;
  try (intros HH; discriminate HH); auto; generalize (Hrec p4);
  case positive_eq; intros HH; try (subst p3; auto; fail);
  intros HH1; case HH; injection HH1; auto.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*             Some modulo-3 operations for positive                         *)
(*                                                                           *)
(*****************************************************************************)

Definition pos_up x := 
  match x with
  | 1%positive => 2%positive
  | 2%positive => 3%positive
  | _ => 1%positive
  end.

Definition pos_down x := 
  match x with
  | 2%positive => 1%positive
  | 3%positive => 2%positive
  | _ => 3%positive
  end.

Lemma pos_up_less_4 s : (pos_up s < 4)%positive.
Proof.
case s; simpl; try (intros; red; simpl; auto; fail).
intros p; case p; simpl; try (intros; red; simpl; auto; fail).
Qed.

Lemma pos_up_mod_3 s : (s < 4)%positive ->
  (Z.pred (Zpos (pos_up s)) mod 3 =  (1 + Z.pred (Z.pos s)) mod 3)%Z.
Proof.
case s; simpl; auto; intros p; case p; simpl; auto;
intros p1; case p1; unfold Pos.lt; intros; discriminate.
Qed.

Lemma pos_down_less_4 s : (pos_down s < 4)%positive.
Proof.
case s; simpl; try (intros; red; simpl; auto; fail).
- intros p; case p; simpl; try (intros; red; simpl; auto; fail).
- intros p; case p; simpl; try (intros; red; simpl; auto; fail).
Qed.

Lemma pos_down_mod_3 s : (s < 4)%positive ->
  (Z.pred (Zpos (pos_down s)) mod 3 =  (2 + Z.pred (Zpos s)) mod 3)%Z.
Proof.
case s; simpl; auto; intros p; case p; simpl; auto;
intros p1; case p1; unfold Pos.lt; intros; discriminate.
Qed.

Lemma pos_down_up s : (s < 4 -> pos_down (pos_up s) = s)%positive.
Proof.
case s; simpl; auto; intros p; case p; simpl; auto;
  intros p1; case p1; auto; intros; discriminate.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                   The seven cubes                                         *)
(*                                                                           *)
(*****************************************************************************)

Inductive cube := C1 | C2 | C3 | C4 | C5 | C6 | C7.

Lemma unique7: unique (C1 :: C2 :: C3 :: C4 :: C5 :: C6 :: C7 :: nil).
Proof.
repeat apply uniqC; try apply uniqN; auto with datatypes;
  simpl; intuition; discriminate.
Qed.

Definition c2N e := match e with 
  C1 => 0 | C2 => 1 | C3 => 2 | C4 => 3 | C5 => 4 | C6 => 5 | C7 => 6 
  end.

Local Definition N2c n := match n with 
  0 => C1 | 1 => C2 | 2 => C3 | 3 => C4 | 4 => C5 | 5 => C6 | _ => C7
  end.

Local Definition dummy {S1 : Type} (S2 :  Type) (e : S1) := S2.

Let cube_pred_aux (c : cube) : cube.
change cube with (dummy cube c).
case c; match goal with |- dummy _ ?n  =>
  let e := eval compute in (N2c (pred (c2N n))) in
  exact e
end.
Defined.

Definition cube_pred (c : cube) :=
  Eval lazy in cube_pred_aux c.

Let cube_succ_aux (c : cube) : dummy cube c.
case c; match goal with |- dummy _ ?n  =>
  let e := eval compute in (N2c (S (c2N n))) in
  exact e
end.
Defined.

Definition cube_succ c := Eval lazy in cube_succ_aux c.

Let cube_compare_aux (c1 c2 : cube) : dummy comparison (c1,c2).
case c1; case c2; match goal with |- dummy _ (?n1,?n2)  =>
  let e := eval compute in (Nat.compare (c2N n1) (c2N n2)) in
  exact e
end.
Defined.
Definition cube_compare (c1 c2 : cube) := Eval lazy in cube_compare_aux c1 c2.

Lemma cube_compare_correct c1 c2 :
  match cube_compare c1 c2 with
    | Eq => c1 = c2
    | Lt => (c2N c1 < c2N c2)%nat
    | Gt => (c2N c1 > c2N c2)%nat
  end.
Proof. case c1; case c2; simpl; auto with arith. Qed.

Let cube_encode_aux (c1 c2 : cube) : dummy positive (c1, c2).
case c1; case c2; match goal with |- dummy _ (?n1,?n2)  =>
  let e := eval compute in (P_of_succ_nat (5 * c2N n2 + c2N n1)) in
  exact e
end.
Defined.

Definition cube_encode (c1 c2 : cube) :=
 Eval lazy in cube_encode_aux c1 c2.

Let cube_decode_aux (p: positive) : dummy (cube * cube) p.
revert p.
do 5 try (intro p; case p; clear p); try (intros p; exact (C1 , C1));
match goal with |- dummy _ ?n =>
  let z1 := eval compute in ((Zpos n - 1) mod 5)%Z in
  let z2 := eval compute in ((Zpos n - 1) / 5)%Z in
  let e := eval compute in (N2c (Z.abs_nat z1), N2c (Z.abs_nat z2)) in
  exact e
end.
Defined.

Definition cube_decode (p: positive) :=
  Eval lazy in cube_decode_aux p.

Lemma cube_encode_decode c1 c2 : 
 c2N c1 - 4 = 0 -> c2N c2 - 5 = 0 -> cube_decode (cube_encode c1 c2) = (c1, c2).
Proof.
case c1; case c2; simpl; auto; intros; try discriminate.
Qed.

Let cube3_encode_aux (c0 c1 c2 : cube) : 
  dummy positive (c0,c1,c2).
case c0; case c1; case c2; match goal with |- dummy _ (?n0, ?n1,?n2)  =>
  let e := eval compute in (P_of_succ_nat (30 * c2N n0 + 6 * c2N n1 + c2N n2)) in
  exact e
end.
Defined.

Definition cube3_encode c0 c1 c2 := Eval lazy in cube3_encode_aux c0 c1 c2.

Let cube3_decode_aux (p: positive) : dummy (cube * cube * cube) p.
revert p.
do 6 try (intros p; case p; clear p); try (intros p; exact (C1, C1 , C1));
match goal with |- dummy _ ?n =>
  exact (
  let z1 := ((Zpos n - 1) mod 6)%Z in
  let z2 := ((Zpos n - 1) / 6)%Z in
  let z3 := (z2 mod 5)%Z in
  let z4 := (z2 / 5)%Z in
    (N2c (Z.abs_nat z4), N2c (Z.abs_nat z3), N2c (Z.abs_nat z1)))
end.
Defined.

Definition cube3_decode p := Eval lazy in  cube3_decode_aux p.

Lemma cube3_encode_decode c0 c1 c2 : 
c2N c0 - 1 = 0 -> 
c2N c1 - 4 = 0 ->
c2N c2 - 5 = 0 -> cube3_decode (cube3_encode c0 c1 c2) = (c0, c1, c2).
Proof.
case c0; case c1; case c2; simpl; auto; intros; try discriminate.
Qed.

Definition cube_eq c1 c2 := 
  match cube_compare c1 c2 with Eq => true | _ => false end.

Lemma cube_eq_correct c1 c2 : if cube_eq c1 c2 then c1 = c2 else c1 <> c2.
Proof.
case c1; case c2; simpl; auto; intros; discriminate.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                   The 3 Orientations                                      *)
(*                                                                           *)
(*****************************************************************************)

Inductive orientation := O1 | O2 | O3.

Definition o2N e := match e with 
  O1 => 0 | O2 => 1 | O3 => 2
  end.

Local Definition N2o n := match n with 
  0 => O1 | 1 => O2 | _ => O3 
  end.

Definition oup o := match o with O1 => O2 | O2 => O3 | O3 => O1 end.

Definition odown o := match o with O1 => O3 | O2 => O1 | O3 => O2 end.

Definition oinv o := match o with O1 => O1 | O2 => O3 | O3 => O2 end.

Definition oadd o1 o2 := match o1 with O1 => o2 | O2 => oup o2 | o3 => odown o2 end.

Definition o2Z o := match o with O1 => 0%Z | O2 => 1%Z | o3 => 2%Z end.

Definition oeq o1 o2 :=
   match o1, o2 with
   | O1, O1 => true
   | O2, O2 => true
   | O3, O3 => true
   | _, _ => false 
   end.

Lemma oeq_correct o1 o2 :
  if oeq o1 o2 then o1 = o2 else o1 <> o2.
Proof.
case o1; case o2; simpl; auto; intros; discriminate.
Qed.

Lemma oup_mod_3 o : (o2Z (oup o) mod 3 = (o2Z o + 1) mod 3)%Z.
Proof.
case o; simpl; auto.
Qed.

Lemma odown_mod_3 o : (o2Z (odown o) mod 3 = (o2Z o - 1) mod 3)%Z.
Proof.
case o; simpl; auto.
Qed.

Lemma oadd_mod_3 ox oy : 
 (o2Z (oadd ox oy) mod 3 =  (o2Z ox mod 3 + o2Z oy mod 3) mod 3)%Z.
Proof.
case ox; case oy; simpl; auto.
Qed.

Lemma oinv_eq ox oy : oadd ox oy = O1 -> oinv ox = oy.
Proof.
case ox; case oy; simpl; auto; intros; discriminate.
Qed.

Lemma eq_mod_3 ox oy : (o2Z ox mod 3 =  o2Z oy mod 3)%Z -> ox = oy.
Proof.
case ox; case oy; simpl; auto; intros; discriminate.
Qed.

Lemma oup_down o : oup (odown o) = o.
Proof. case o; simpl; auto. Qed.

Lemma odown_up o : odown (oup o) = o.
Proof. case o; simpl; auto. Qed.


(*****************************************************************************)
(*                                                                           *)
(*                         State                                             *)
(*                                                                           *)
(*****************************************************************************)


Inductive state := 
  State (c1 c2 c3 c4 c5 c6 c7 : cube) 
        (o1 o2 o3 o4 o5 o6 o7 : orientation).

Definition init_state := State C1 C2 C3 C4 C5 C6 C7 O1 O1 O1 O1 O1 O1 O1.

Definition valid_state s := 
  match s with
  | State c1 c2 c3 c4 c5 c6 c7 o1 o2 o3 o4 o5 o6 o7 =>
     perm (C1 :: C2 :: C3 :: C4 :: C5 :: C6 :: C7 :: nil)
          (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: nil) /\
     fold_left oadd
             (o1 :: o2 :: o3 :: o4 :: o5 :: o6 :: o7 :: nil) O1 = O1
  end.

Lemma valid_state_init : valid_state init_state.
Proof.
simpl; repeat split; auto.
apply perm_id.
Qed.

Definition state_eq (s1 s2: state) :=
  match s1, s2 with 
   State p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14, 
   State q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14  => 
   (cube_eq p1 q1 && cube_eq p2 q2 && cube_eq p3 q3 &&
    cube_eq p4 q4 && cube_eq p5 q5 && cube_eq p6 q6 && cube_eq p7 q7 &&
    oeq p8 q8 && oeq p9 q9 && oeq p10 q10 &&  oeq p11 q11 &&
    oeq p12 q12 && oeq p13 q13 && oeq p14 q14)%bool
   end.

Lemma state_eq_correct s1 s2 :
  if state_eq s1 s2 then s1 = s2 else s1 <> s2.
Proof.
case s1; case s2; intros; unfold state_eq.
repeat match goal with |- context[cube_eq ?X ?Y] =>
  generalize (cube_eq_correct X Y); case cube_eq;
  [idtac | intros HH HH1; case HH; injection HH1; auto];
  intros; subst Y
end; simpl; auto.
repeat match goal with |- context[oeq ?X ?Y] =>
  generalize (oeq_correct X Y); case oeq;
  [idtac | intros HH HH1; case HH; injection HH1; auto];
  intros; subst Y
end; simpl; auto.
Qed.

Local Definition states := list state.

Fixpoint in_states s (ls : states) {struct ls} : bool :=
  match ls with
  | nil => false
  | cons s1 ls1 => if state_eq s s1 then true else in_states s ls1
  end.

Lemma in_states_correct s ls : 
  if in_states s ls then In s ls else ~In s ls.
Proof.
elim ls; simpl; auto.
intros a l1 Hrec; generalize (state_eq_correct s a); case state_eq; auto.
intros H1; generalize Hrec; case in_states; auto.
intros HH [HH1 | HH1]; case H1; auto; case HH; auto.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                         Rotations                                         *)
(*                                                                           *)
(*****************************************************************************)


(** Right Rotation: 1 -(-1)-> 4 -(+1)-> 5 -(-1)-> 2 -(+1)-> 1 **)
Definition rright s :=
  match s with
  | State p1 p2 p3 p4 p5 p6 p7 o1 o2 o3 o4 o5 o6 o7 =>
    State p2 p5 p3 p1 p4 p6 p7 (oup o2) (odown o5) o3 (odown o1) (oup o4) o6 o7
  end.

Eval compute in rright init_state.

(** Back Rotation: 4 -(-1)-> 7 -(+1)-> 6 -(-1)-> 5 -(+1)-> 4 **)
Definition rback s := 
  match s with
  | State p1 p2 p3 p4 p5 p6 p7 o1 o2 o3 o4 o5 o6 o7 =>
    State p1 p2 p3 p5 p6 p7 p4 o1 o2 o3 (oup o5) (odown o6) (oup o7) (odown o4)
  end.

Eval compute in rback init_state.

(** Down Rotation: 2 -(+0)-> 5 -(+0)-> 6 -(+0)-> 3 -(+0)-> 2 **)
Definition rdown s := 
  match s with
  | State p1 p2 p3 p4 p5 p6 p7 o1 o2 o3 o4 o5 o6 o7 =>
    State p1 p3 p6 p4 p2 p5 p7 o1 o3 o6 o4 o2 o5 o7
  end.

Eval compute in rdown init_state.

Ltac Zmod_plus_tac H :=
  match H with
  | ((?X mod 3 + ?Y mod 3) mod 3)%Z => 
    let X1 := constr:((X mod 3)%Z) in
    let Y1 :=  constr:((Y mod 3)%Z) in
    Zmod_plus_tac X1 || Zmod_plus_tac Y1 || rewrite <- (Zplus_mod X Y 3)
  | _ => idtac 
  end.

Lemma valid_state_right s : valid_state s -> valid_state (rright s).
Proof.
case s; unfold valid_state, rright, fold_left; 
  intros p1 p2 p3 p4 p5 p6 p7 o1 o2 o3 o4 o5 o6 o7 (H1, H2).
split.
- apply perm_trans with (1 := H1).
  refine (perm_trans _ _ _ (perm_swap _ _ _) _).
  apply perm_skip.
  refine (perm_trans _ _ _ (perm_swap _ _ _) _).
  refine (perm_trans _ _ _ _ (perm_swap _ _ _)).
  apply perm_skip.
  refine (perm_trans _ _ _ _ (perm_swap _ _ _)).
  apply perm_skip.
  refine (perm_trans _ _ _ _ (perm_swap _ _ _)).
  apply perm_id.
- apply trans_equal with (2 := H2).
  apply eq_mod_3; auto; try (red; auto; fail).
  repeat rewrite oadd_mod_3 || rewrite oup_mod_3 || rewrite odown_mod_3.
  simpl.
  repeat rewrite Zmod_mod.
  do 7 match goal with |- ?X = _  => Zmod_plus_tac X end.
  do 7 match goal with |- _ = ?X  => Zmod_plus_tac X end.
  apply f_equal2 with (f := Zmod); auto.
  ring.
Qed.

Lemma valid_state_back s : valid_state s -> valid_state (rback s).
Proof.
case s; unfold valid_state, rright, fold_left; 
  intros p1 p2 p3 p4 p5 p6 p7 o1 o2 o3 o4 o5 o6 o7 (H1, H2).
split.
- apply perm_trans with (1 := H1).
  do 3 apply perm_skip.
  refine (perm_trans _ _ _ (perm_swap _ _ _) _).
  apply perm_skip.
  refine (perm_trans _ _ _ (perm_swap _ _ _) _).
  apply perm_skip.
  refine (perm_trans _ _ _ (perm_swap _ _ _) _).
  apply perm_id.
- apply trans_equal with (2 := H2).
  apply eq_mod_3; auto; try (red; auto; fail).
  repeat rewrite oadd_mod_3 || rewrite oup_mod_3 || rewrite odown_mod_3.
  simpl.
  repeat rewrite Zmod_mod.
  do 7 match goal with |- ?X = _  => Zmod_plus_tac X end.
  do 7 match goal with |- _ = ?X  => Zmod_plus_tac X end.
  apply f_equal2 with (f := Zmod); auto.
  ring.
Qed.

Lemma valid_state_down s : valid_state s -> valid_state (rdown s).
Proof.
case s; unfold valid_state, rright, fold_left; 
  intros p1 p2 p3 p4 p5 p6 p7 o1 o2 o3 o4 o5 o6 o7 (H1, H2).
split.
- apply perm_trans with (1 := H1).
  apply perm_skip.
  refine (perm_trans _ _ _ (perm_swap _ _ _) _).
  apply perm_skip.
  refine (perm_trans _ _ _ _ (perm_swap _ _ _)).
  refine (perm_trans _ _ _ (perm_swap _ _ _) _).
  apply perm_skip.
  refine (perm_trans _ _ _ _ (perm_swap _ _ _)).
  apply perm_skip.
  refine (perm_trans _ _ _ _ (perm_swap _ _ _)).
  apply perm_id.
- apply trans_equal with (2 := H2).
  apply eq_mod_3; auto; try (red; auto; fail).
  repeat rewrite oadd_mod_3 || rewrite oup_mod_3 || rewrite odown_mod_3.
  simpl.
  repeat rewrite Zmod_mod.
  do 7 match goal with |- ?X = _  => Zmod_plus_tac X end.
  do 7 match goal with |- _ = ?X  => Zmod_plus_tac X end.
  apply f_equal2 with (f := Zmod); auto.
  ring.
Qed.

Lemma right_4 s : rright (rright (rright (rright s))) = s.
Proof.
case s; simpl; intros.
repeat rewrite oup_down; repeat rewrite odown_up; auto.
Qed.

Lemma back_4 s : rback (rback (rback (rback s))) = s.
Proof.
case s; simpl; intros.
repeat rewrite oup_down; repeat rewrite odown_up; auto.
Qed.

Lemma down_4 s : rdown (rdown (rdown (rdown s))) = s.
Proof.
case s; simpl; intros.
repeat rewrite oup_down; repeat rewrite odown_up; auto.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                         Reachability                                      *)
(*                                                                           *)
(*****************************************************************************)


Inductive reachable : state -> Prop :=
  reach0: reachable init_state
| reachr: forall s, reachable s -> reachable (rright s)
| reachb: forall s, reachable s -> reachable (rback s)
| reachd: forall s, reachable s -> reachable (rdown s).

Lemma reachable_valid s : reachable s -> valid_state s.
Proof.
intros H; elim H; auto.
- apply valid_state_init.
- intros; apply valid_state_right; auto.
- intros; apply valid_state_back; auto.
- intros; apply valid_state_down; auto.
Qed.

Definition move (s1 s2 : state) :=
  s2 = rright s1  \/
  s2 = rright (rright s1) \/
  s2 = rright (rright (rright s1)) \/
  s2 = rback s1 \/
  s2 = rback (rback s1) \/
  s2 = rback (rback (rback s1)) \/
  s2 = rdown s1 \/
  s2 = rdown (rdown s1) \/
  s2 = rdown (rdown (rdown s1)).

Lemma move_valid s1 s2 : valid_state s1 -> move s1 s2 -> valid_state s2.
Proof.
intros Hg [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]]];
  subst s2; repeat (apply valid_state_right || apply valid_state_back 
                                            || apply valid_state_down; auto).
Qed.

Lemma move_sym s1 s2 : valid_state s1 -> move s1 s2 -> move s2 s1.
Proof.
intros Hg [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]]];
  subst s2;
try (pattern s1 at 2; rewrite <- right_4; unfold move; auto; fail);
try (pattern s1 at 2; rewrite <- down_4; auto; unfold move; do 6 right; auto; fail);
pattern s1 at 2; rewrite <- back_4; auto; unfold move; do 3 right; auto.
Qed.

Inductive nreachable: nat -> state -> Prop :=
| nreach0: nreachable 0 init_state
| nreachS: forall n s1 s2, 
     nreachable n s1 -> move s1 s2 -> nreachable (S n) s2.

Lemma nreachable_reachable n s : nreachable n s -> reachable s.
Proof.
intros H; elim H; clear n s H; intros; auto.
apply reach0.
generalize H1; clear H1; 
  intros [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]]];
  subst s2; repeat apply reachr; repeat apply reachb;
   repeat apply reachd; auto.
Qed.

Lemma reachable_nreachable s : reachable s -> exists n, nreachable n s.
Proof.
intros H; elim H; clear s H; try (exists 0%nat; apply nreach0);
  intros s Hs (n, Hrec); exists (S n); apply nreachS with s; auto;
  unfold move; auto; do 6 right; auto.
Qed.

Lemma move_nreachable n s2 :
  nreachable (S n) s2 -> exists s1, move s1 s2 /\ nreachable n s1.
Proof.
intros H; inversion_clear H as [| xx s1 yy Hs1 Hs2];
  exists s1; auto.
Qed.

Lemma nreachable_valid n s : nreachable n s -> valid_state s.
Proof.
intros H; elim H; clear n s H.
apply valid_state_init.
intros n s1 s2 H1 H2 H3; apply move_valid with s1; auto.
Qed.

Definition nreachable_dec n s :
   valid_state s -> {nreachable n s} + {~nreachable n s}.
Proof.
revert s; elim n; simpl; auto.
- intros s; generalize (state_eq_correct s init_state); case state_eq; intros HH.
  * left; rewrite HH; apply nreach0.
  * right; intros HH1; case HH; inversion_clear HH1; auto.
- intros n1 Hrec s Hg.
  case (Hrec (rright s)); try intros H1.
  * apply valid_state_right; auto.
  * left; rewrite <- right_4; try apply nreachr3; auto.
    apply nreachS with (1 := H1); unfold move; auto.
  * case (Hrec (rright (rright s))); try intros H2.
    + repeat apply valid_state_right; auto.
    + left; rewrite <- right_4; try apply nreachr2; auto.
      apply nreachS with (1 := H2); unfold move; auto.
    + case (Hrec (rright (rright (rright s)))); try intros H3.
    -- repeat apply valid_state_right; auto.
    -- left; rewrite <- right_4; try apply nreachr1; auto.
       apply nreachS with (1 := H3); unfold move; auto.
    -- case (Hrec (rback s)); try intros H4.
       ** apply valid_state_back; auto.
       ** left; rewrite <- back_4; try apply nreachb3; auto.
          apply nreachS with (1 := H4); unfold move; do 3 right; auto.
       ** case (Hrec (rback (rback s))); try intros H5.
          ++ repeat apply valid_state_back; auto.
          ++ left; rewrite <- back_4; try apply nreachb2; auto.
             apply nreachS with (1 := H5); unfold move; do 3 right; auto.
          ++ case (Hrec (rback (rback (rback s)))); try intros H6.
             --- repeat apply valid_state_back; auto.
             --- left; rewrite <- back_4; try apply nreachb1; auto.
                 apply nreachS with (1 := H6); unfold move; do 3 right; auto.
             --- case (Hrec (rdown s)); try intros H7.
                 *** apply valid_state_down; auto.
                 *** left; rewrite <- down_4; try apply nreachd3; auto.
                     apply nreachS with (1 := H7); unfold move;
                     do 6 right; auto.
                 *** case (Hrec (rdown (rdown s))); try intros H8.
                     ++++ repeat apply valid_state_down; auto.
                     ++++ left; rewrite <- down_4; try apply nreachd2; auto.
                          apply nreachS with (1 := H8); 
                          unfold move; do 6 right; auto.
                     ++++ case (Hrec (rdown (rdown (rdown s)))); try intros H9.
                          ---- repeat apply valid_state_down; auto.
                          ---- left; rewrite <- down_4; 
                                 try apply nreachd1; auto.
                               apply nreachS with (1 := H9); 
                               unfold move; do 6 right; auto.
                          ---- right; intros H10.
                               case (move_nreachable _ _ H10); 
                                   intros s1 HH; case HH; clear HH.
                               intros [HH1 | [HH1 | [HH1 | [HH1 | [HH1 | 
                                      [HH1 | [HH1 | [HH1 | HH1]]]]]]]] HH2; 
                                      subst s.
                               **** case H3; rewrite right_4; auto; 
                                    apply nreachable_valid with n1; auto.
                               **** case H2; rewrite right_4; auto; 
                                    apply nreachable_valid with n1; auto.
                               **** case H1; rewrite right_4; auto; 
                                    apply nreachable_valid with n1; auto.
                               **** case H6; rewrite back_4; auto; 
                                    apply nreachable_valid with n1; auto.
                               **** case H5; rewrite back_4; auto; 
                                    apply nreachable_valid with n1; auto.
                               **** case H4; rewrite back_4; auto; 
                                    apply nreachable_valid with n1; auto.
                               **** case H9; rewrite down_4; auto; 
                                    apply nreachable_valid with n1; auto.
                               **** case H8; rewrite down_4; auto; 
                                    apply nreachable_valid with n1; auto.
                               **** case H7; rewrite down_4; auto; 
                                    apply nreachable_valid with n1; auto.
Qed.

Definition nreachable_le_dec n s :
  valid_state s -> 
  {forall m, m < n -> ~ nreachable m s} + {exists m, m < n /\ nreachable m s}.
Proof.
intro Hs; elim n; simpl; clear n.
- left; intros m Hm; contradict Hm; auto with arith.
- intros n [Hrec | Hrec].
  case (nreachable_dec n s); auto; intros H1.
  + right; exists n; auto.
  + left; intros m Hm; inversion Hm; auto.
  + right; case Hrec; intros m (Hm1, Hm2); exists m; split; auto with arith.
Qed.

Definition nsreachable n s :=
  nreachable n s /\ forall m, m < n -> ~ nreachable m s.

Lemma nsreachable_unique n m s : nsreachable n s -> nsreachable m s -> n = m.
Proof.
intros (H1, H2) (H3, H4).
case (le_or_lt n m); intros HH0.
- case (le_lt_or_eq _ _ HH0); clear HH0; intros HH0; auto.
  case (H4 n); auto.
- case (H2 m); auto.
Qed.

Lemma nsreachable_bound n s :
  nreachable n s -> exists m, m <= n /\ nsreachable m s.
Proof.
revert s; pattern n; apply Wf_nat.lt_wf_ind; clear n.
intros n; case n; clear n.
- intros _ s H; exists 0; split; auto with arith.
  split; auto; intros m Hm; contradict Hm; auto with arith.
- intros n Hrec s Hs.
  case (nreachable_le_dec  (S n) s).
  + apply nreachable_valid with (1 := Hs).
  + intros H1; exists (S n); split; auto; split; auto.
  + intros (m, (Hm1, Hm2)).
    case (Hrec _ Hm1 _ Hm2); intros s1 (Hs1, Hs2).
    exists s1; split; auto with arith.
    apply le_trans with (1 := Hs1); auto with arith.
Qed.

Lemma move_nsreachable n s2 :
  nsreachable (S n) s2 -> exists s1, move s1 s2 /\ nsreachable n s1.
Proof.
intros (H1, H2).
case (move_nreachable _ _ H1); intros s1 (Hs1, Hs2).
exists s1; split; auto.
case (nsreachable_bound _ _ Hs2); intros m (Hm, Hm1).
case (le_lt_or_eq _ _ Hm); clear Hm; intros Hm.
- case (H2 (S m)); auto with arith.
  apply nreachS with (2 := Hs1); auto.
  case Hm1; auto.
- subst n; auto.
Qed.

Lemma nsreachable_inv n m s :
  n <= m -> nsreachable m s -> exists s1, nsreachable n s1.
Proof.
intro H; revert s; elim H; auto; clear m H.
- intros s H1; exists s; auto.
- intros m _ H1 s H2.
  case (move_nsreachable _ _ H2); intros s1 (_, Hs1); auto.
  apply (H1 s1); auto.
Qed.

Definition nlreachable n s := exists m, m <= n /\ nreachable m s.

Lemma nlreachable_reachable n s : nlreachable n s -> reachable s.
Proof.
intros (m, (Hm, Hm1)).
apply nreachable_reachable with m; auto.
Qed.

Lemma nlreach_weak n m s : 
  n <= m -> nlreachable n s -> nlreachable m s.
Proof.
intros H (m1, (Hm1, Hm2)).
exists m1; split; auto.
apply le_trans with (1 := Hm1); auto.
Qed.

Lemma nlreachable_bound n s :
  nlreachable n s -> exists m, m <= n /\ nsreachable m s.
Proof.
intros (m, (H1, H2)); case (nsreachable_bound m s); auto.
intros p (Hp, Hp1); exists p; split; auto.
apply le_trans with (1 := Hp); auto.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*       Computational version of reachability                               *)
(*                                                                           *)
(*****************************************************************************)

(* The list of all moves *)
Definition movel :=
 rright :: (fun s1 => rright (rright s1)) :: 
           (fun s1 => rright (rright (rright s1))) ::
 rback :: (fun s1 => rback (rback s1)) :: 
          (fun s1 => rback (rback (rback s1))) ::
 rdown:: (fun s1 => rdown (rdown s1)) :: 
         (fun s1 => rdown (rdown (rdown s1))):: nil.

(* The list of candidate *)
Definition candidate_list l := 
  fold_right
      (fun (y : state) (x : list state) =>
        map (fun y1 : state -> state => y1 y) movel ++ x) nil l.

(* A filter that only adds the element that were not already in the first list *)
Definition filters (ps : states * states) (s : state) :=
          let (states, nstates) := ps in
          if in_states s states then ps
          else (s :: states, s :: nstates).

(* Compute the next pair of states *)
Definition nexts (ps : states * states) s :=
 fold_left 
  (fun (ps : states * states) f => 
    let (states, nstates) := ps in
    let s := f s in
    if in_states s states then ps else
    let states1 := s :: states in
    let nstates1 := s :: nstates in (states1, nstates1))
   movel ps.

(* Now we just iterate *)

Fixpoint iters_aux n (ps : states * states) := 
  match n with 
  | O    => ps 
  | S n1 => let (m,p) := ps in 
            iters_aux n1 (fold_left nexts p (m,nil))
  end.

Definition iters n := iters_aux n (init_state :: nil, init_state :: nil).

(*****************************************************************************)
(*              Proving iters                                                *)
(*****************************************************************************)

Lemma movel_valid f s :
   In f movel -> valid_state s -> valid_state (f s).
Proof.
intros [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]]]]; 
  try subst f;
  intros; repeat apply valid_state_right; 
   repeat apply valid_state_back;
   repeat apply valid_state_down; auto.
case H1; auto.
Qed.

Lemma candidate_list_correct l n :
  (forall i, (nsreachable n i -> In i l) /\ 
            (In i l -> nlreachable n i)) ->
  (forall i, (nsreachable (S n) i -> In i (candidate_list l)) /\
            (In i (candidate_list l) -> nlreachable (S n) i)).
Proof.
assert (F : forall l n i, 
     (forall j, move j i -> nsreachable n j -> In j l) ->
      nsreachable (S n) i -> In i (candidate_list l)).
- intros l1; elim l1; simpl; auto; clear l1.
  + intros n1 i1 H Hi1.
    case (move_nsreachable _ _ Hi1); intros j1 (Hj1, Hj2); auto.
    apply (H j1); auto.
  + intros s l1 Hrec n1 i1 Hi Hi1.
    case (move_nsreachable _ _ Hi1); intros j1 (Hj1, Hj2); auto.
    case (Hi _ Hj1 Hj2); intros HH.
    * rewrite <-HH in Hj1; unfold move in Hj1; clear HH; intuition.
    * do 9 match goal with |- context[?X = ?Y] =>
              generalize (state_eq_correct X Y); 
              case state_eq; auto; intros; right
           end.
      apply Hrec with n1; auto.
      intros j Hj3 Hj4.
      case  (Hi _ Hj3 Hj4); auto.
      intros HH1; rewrite <- HH1 in Hj3.
      do 8 (case Hj3; intros HH2; contradict HH2; auto; 
            clear Hj3; intros Hj3).
- intros H i; split.
  + intros; apply F with n; auto.
    intros; case (H j); auto.
  +  assert (H1: forall i, In i l -> nlreachable n i).
       intros i1; case (H i1); auto.
     generalize H1; elim l; simpl; auto; clear l H H1.
     * intros _ HH; case HH.
     * intros a l Hrec; intros H1.
       case (H1 a); auto; intros m (Hm, Hm1).
       intros [HH1 | [HH1 | [HH1 | [HH1 | 
              [HH1 | [HH1 | [HH1 | [HH1 | [HH1 | HH1]]]]]]]]];
       try (subst i; exists (S m); split; auto with arith;
         apply nreachS with (1 := Hm1); unfold move; auto; 
         do 3 right; auto; do 3 right; auto).
       apply Hrec; auto.
Qed.

Lemma candidate_valid l :
  (forall s, In s l -> valid_state s) ->
  (forall s, In s (candidate_list l) -> valid_state s).
Proof.
elim l; unfold candidate_list; auto; clear l.
intros a l Hrec Hg s; rewrite fold_right_cons; intros H1.
case (in_app_or _ _ _ H1); intros H2; auto with datatypes.
assert (F0: valid_state a); auto with datatypes.
rewrite in_map_iff in H2.
case H2; intros f (Hf, Hf1); subst s.
apply movel_valid; auto.
Qed.

Lemma candidate_app l1 l2 :
 candidate_list (l1 ++ l2) = candidate_list l1 ++ candidate_list l2.
Proof.
revert l2; elim l1; unfold candidate_list; clear l1.
- simpl; auto.
- intros a l1 Hrec l2; rewrite fold_right_cons.
  rewrite app_ass, <- Hrec; auto.
Qed.

Lemma candidate_in a l :
  In a (candidate_list l) <-> 
  exists i, exists f, a = f i /\ In i l /\ In f movel.
Proof.
elim l; clear l.
- split; intros H; case H; intros i (f, (_, (HH,_))); case HH.
- intros b l Hrec; split.
  + intros H; case (in_app_or (map (fun y1 : state -> state => y1 b) movel)
                           (candidate_list l) _ H).
    * elim movel; simpl; auto.
      -- intros HH; case HH.
      -- intros f lf Hrec1 [H1 | H1].
         ++ exists b; exists f; auto.
         ++ case (Hrec1 H1); intros f1 (b1, (Hb1, (Hb2, Hb3))).
            exists f1; exists b1; auto.
    * rewrite Hrec; intros (i, (f, (Hb1, (Hb2, Hb3)))).
      exists i; exists f; auto with datatypes.
  + intros (i, (f, (Hf, (Hf1, Hf2)))); subst a.
    unfold candidate_list; rewrite fold_right_cons.
    match goal with |- context[fold_right ?X ?Y ?Z] =>
     change (fold_right X Y Z) with (candidate_list Z)
    end.
    apply in_or_app.
    simpl in Hf1; case Hf1; clear Hf1; intros Hf1.
    * subst b; left; generalize Hf2; elim movel; simpl; auto.
      intros f1 lf Hrec1 [H1 | H1]; auto; subst f1; auto.
    * right; rewrite Hrec.
      exists i; exists f; auto.
Qed.

Definition lequiv {A : Type} l1 l2:= forall s : A, In s l1 <-> In s l2.

Definition pequiv {A : Type} (pl1 pl2 : list A * list A) := 
  lequiv (fst pl1) (fst pl2) /\ lequiv (snd pl1) (snd pl2).

Lemma candidate_equiv l1 l2 :
  lequiv l1 l2 -> lequiv (candidate_list l1) (candidate_list l2).
Proof.
intros H1 a.
repeat rewrite candidate_in.
split; intros (i, (f, (Hf, (Hf1, Hf2)))); exists i; exists f; auto.
- repeat split; auto; unfold lequiv in H1; rewrite <- H1; auto.
- repeat split; auto; unfold lequiv in H1; rewrite H1; auto.
Qed.

Definition valid_pair ps :=
  (forall s, In s (fst ps) -> valid_state s) /\
  (forall s, In s (snd ps) -> valid_state s).

Lemma filters_valid ps s1 :
  valid_pair ps -> valid_state s1 -> valid_pair (filters ps s1).
Proof.
destruct ps as (ss1, ss2); intros (Hg1, Hg2) Hg; split; intros s;
   unfold filters; case in_states; simpl; auto; 
   intros [H1 | H1]; auto; subst s1; auto.
Qed.

Lemma filters_incl ps s :
  incl (snd ps) (fst ps) ->
  incl (snd (filters ps s)) (fst (filters ps s)).
Proof.
destruct ps as (ss1, ss2); intro H; unfold filters.
case in_states; simpl; auto with datatypes.
Qed.

Lemma filters_correct ps l :
 let ps1 := fold_left filters l ps in
 (forall i, In i (fst ps1) <-> In i (fst ps) \/ In i l) /\
 (forall i, In i (snd ps1) <-> In i (snd ps) \/ (~In i (fst ps) /\ In i l)).
Proof.
revert ps; elim l; clear l; simpl; auto.
- intros ps; split; intros i; split; auto.
  + intros [HH | HH]; auto; case HH.
  + intros [HH | HH]; auto; case HH; intros _ HH1; case HH1.
- intros a l Hrec ps.
  case (Hrec (filters ps a)); intros H1 H2; split.
  + intros i; apply iff_trans with (1:= H1 i).
    unfold filter; case ps; simpl; intros s1 s2.
    generalize (in_states_correct a s1); case in_states; simpl; auto.
    * intros H5; split; intros [HH | HH]; auto.
      case HH; auto; intros; subst i; auto.
    * intros H5; split; intros [HH | HH]; auto.
      -- case HH; auto.
      -- case HH; auto.
  + intros i; apply iff_trans with (1:= H2 i).
    unfold filter; case ps; simpl; intros s1 s2.
    generalize (in_states_correct a s1); case in_states; simpl; auto.
    * intros H5; split; intros [HH | HH]; auto.
      -- case HH; auto.
      -- case HH; intros HH1 [HH2 | HH2]; auto.
         case HH1; rewrite <- HH2; auto.
    * intros H5; split; intros [HH | HH]; auto.
      -- case HH; auto; intros; subst i; auto.
      -- case HH; intros HH1 HH2; right; auto.
      -- generalize (state_eq_correct a i); 
          case state_eq; auto; intros He.
         case HH; intros HH1 [HH2 | HH2]; auto.
         right; split; auto.
         intros [HH3 | HH3]; auto.
Qed.

Lemma filters_equiv ps1 ps2 l1 l2 :
  pequiv ps1 ps2 -> lequiv l1 l2 ->
  pequiv (fold_left filters l1 ps1) (fold_left filters l2 ps2).
Proof.
intros (H1, H2) H3.
case (filters_correct ps1 l1); intros Hr1 Hs1.
case (filters_correct ps2 l2); intros Hr2 Hs2.
split; intros a;
  (rewrite Hr1; rewrite Hr2) ||(rewrite Hs1; rewrite Hs2).
- unfold lequiv in H1, H3; rewrite H1, H3; split; auto.
- unfold lequiv in H1, H2, H3; rewrite H1, H2, H3; split; auto.
Qed.

Definition nexts_correct (ps : states * states) s :
 (forall s1, 
    In s1 (fst (nexts ps s)) <-> 
      In s1 (fst ps) \/ exists f, In f movel /\ s1 = f s /\ ~ In s1 (fst ps)) /\
 (forall s1, 
    In s1 (snd (nexts ps s)) <-> 
      In s1 (snd ps) \/ exists f, In f movel /\ s1 = f s /\ ~ In s1 (fst ps)).
Proof.
unfold nexts.
match goal with |- context[fold_left ?X _ _] =>
  change X with (fun ps f => filters ps (f s))
end.
generalize ps s; elim movel; clear ps s.
- simpl; intros ps s; split; intros s1; split; auto; 
   intros HH; case HH; auto; intros (f, (HH1, _)); case HH1.
- intros f lf Hrec ps s; repeat rewrite fold_left_cons.
  split; intros s1; case (Hrec (filters ps (f s)) s);
    intros Hr1 Hr2.
  + apply iff_trans with (1 := Hr1 s1).
    unfold filters; case ps.
    intros ss1 ss2.
    generalize (in_states_correct (f s) ss1); case in_states.
    * simpl fst; auto.
      intros H1; split; intros [H2 | H2]; auto.
      -- case H2; intros f1 (Hf1, (Hf2, Hf3)).
         right; exists f1; auto with datatypes.
      -- case H2; intros f1 (Hf1, (Hf2, Hf3)).
         simpl in Hf1; case Hf1; clear Hf1; intros Hf1.
         ++ left; rewrite Hf2, <- Hf1; auto.
         ++ right; exists f1; auto with datatypes.
    * simpl fst; auto.
      intros H1; split; intros [H2 | H2]; auto with datatypes.
      -- simpl in  H2; case H2; clear H2; intros H2; auto.
         subst s1; right; exists f; auto with datatypes.
      -- case H2; intros f1 (Hf1, (Hf2, Hf3)).
         right; exists f1; repeat split; auto with datatypes.
      -- case H2; intros f1 (Hf1, (Hf2, Hf3)).
         simpl in Hf1; case Hf1; clear Hf1; intros Hf1.
         ++ subst f1; simpl; auto.
         ++ generalize (state_eq_correct s1 (f s)); case state_eq; intros HH1.
            ** rewrite HH1; auto with datatypes.
            ** right; exists f1; repeat split; auto with datatypes.
               simpl; intros [H3 | H3]; case Hf3; auto.
               case HH1; auto.
  + apply iff_trans with (1 := Hr2 s1).
    unfold filters; case ps.
    intros ss1 ss2.
    generalize (in_states_correct (f s) ss1); case in_states.
    * simpl fst; simpl snd; auto.
      intros H1; split; intros [H2 | H2]; auto.
      -- case H2; intros f1 (Hf1, (Hf2, Hf3)).
         right; exists f1; auto with datatypes.
      -- case H2; intros f1 (Hf1, (Hf2, Hf3)).
         simpl in Hf1; case Hf1; clear Hf1; intros Hf1.
         ++ case Hf3; rewrite Hf2, <- Hf1; auto.
         ++ right; exists f1; auto with datatypes.
    * simpl fst; simpl snd; auto.
      intros H1; split; intros [H2 | H2]; auto with datatypes.
      -- simpl in  H2; case H2; clear H2; intros H2; auto.
         subst s1; right; exists f; auto with datatypes.
      -- case H2; intros f1 (Hf1, (Hf2, Hf3)).
         right; exists f1; repeat split; auto with datatypes.
      -- case H2; intros f1 (Hf1, (Hf2, Hf3)).
         simpl in Hf1; case Hf1; clear Hf1; intros Hf1.
         ++ subst f1; simpl; auto.
         ++ generalize (state_eq_correct s1 (f s)); case state_eq; 
               intros HH1.
            ** rewrite HH1; auto with datatypes.
            ** right; exists f1; repeat split; auto with datatypes.
               simpl; intros [H3 | H3]; case Hf3; auto.
               case HH1; auto.
Qed.

Lemma nexts_equiv ps1 ps2 s :
  pequiv ps1 ps2 -> pequiv (nexts ps1 s) (nexts ps2 s).
Proof.
intros (H1, H2).
case (nexts_correct ps1 s); intros Hr1 Hs1.
case (nexts_correct ps2 s); intros Hr2 Hs2.
split; intros a.
- apply iff_trans with (1 := (Hr1 a)).
  apply iff_sym; apply iff_trans with (1:= (Hr2 a)).
  split; intros [H3 | H3].
  + left; case (H1 a); auto.
  + case H3; intros f1 (Hf1, (Hf2, Hf3)); right; exists f1;
    repeat split; auto; unfold lequiv in H1; rewrite (H1 a); auto.
  + left; case (H1 a); auto.
  + case H3; intros f1 (Hf1, (Hf2, Hf3)); right; exists f1;
    repeat split; auto; intros H4; case Hf3; case (H1 a); auto.
- apply iff_trans with (1 := (Hs1 a)).
  apply iff_sym; apply iff_trans with (1:= (Hs2 a)).
  split; intros [H3 | H3].
  + left; case (H2 a); auto.
  + case H3; intros f1 (Hf1, (Hf2, Hf3)); right; exists f1;
    repeat split; auto; unfold lequiv in H1; rewrite (H1 a); auto.
  + left; case (H2 a); auto.
  + case H3; intros f1 (Hf1, (Hf2, Hf3)); right; exists f1;
    repeat split; auto; intros H4; case Hf3; case (H1 a); auto.
Qed.

Lemma nexts_valid ps s1 :
  valid_pair ps -> valid_state s1 -> valid_pair (nexts ps s1).
Proof.
unfold nexts;
   match goal with |- context[fold_left ?X _ _] =>
    change X with (fun ps f => filters ps (f s1))
   end.
generalize ps s1 (movel_valid); elim movel; auto; clear ps s1.
intros f lf Hrec ps s1 Hf Hg1 Hg; rewrite fold_left_cons.
apply Hrec; auto with datatypes.
generalize (filters_valid ps (f s1) Hg1); auto with datatypes.
Qed.

Lemma nexts_incl ps s :
  incl (snd ps) (fst ps) ->
  incl (snd (nexts ps s)) (fst (nexts ps s)).
Proof.
destruct ps as (ss1, ss2); unfold nexts;
   match goal with |- context[fold_left ?X _ _] =>
    change X with (fun ps f => filters ps (f s))
   end.
generalize ss1 ss2 s; elim movel; auto; clear ss1 ss2 s.
intros f lf Hrec ss1 ss2 s Hs; repeat rewrite fold_left_cons.
generalize (filters_incl (ss1, ss2) (f s)).
case filters; intros ss3 ss4 Hss3.
apply Hrec; auto with datatypes.
Qed.

Lemma fold_nexts_correct ps ss :
  (forall s, In s (fst (fold_left nexts (snd ps) (fst ps, ss))) <->
    In s (fst ps) \/
    (exists f, exists i, In f movel /\ In i (snd ps) /\ s = f i /\ ~ In (f i) (fst ps))) /\
  (forall s, In s (snd (fold_left nexts (snd ps) (fst ps, ss))) <->
    In s ss \/
    (exists f, exists i, In f movel /\ In i (snd ps) /\ s = f i /\ ~ In (f i) (fst ps))).
Proof.
destruct ps as (ss1, ss2); simpl fst; simpl snd.
generalize ss1 ss; elim ss2; clear ss ss1 ss2; auto.
- unfold fold_left, fst, snd.
  intros ss1 ss; split; intros ; split; auto; intros [H1 | H1]; auto;
    case H1; intros f (i, (_, (HH, _))); case HH.
- intros s1 ss2 Hrec ss1 ss.
  rewrite fold_left_cons.
  generalize (nexts_correct (ss1, ss) s1); case nexts; 
    simpl fst; simpl snd; intros ss3 ss4 (Hss3, Hss4).
  assert (tmp: forall A B:Prop, A -> (A -> B) -> A /\ B); auto.
  + apply tmp; clear tmp.
    * intros s; case (Hrec ss3 ss4); intros Hr1 Hr2; clear Hrec.
      apply iff_trans with (1 := Hr1 s).
      split; intros [H1 | H1].
      -- rewrite Hss3 in H1; case H1; auto.
         intros (f, (Hf1, (Hf2, Hf3))); subst s; 
         right; exists f; exists s1;  auto with datatypes.
      -- case H1; intros f (i, (Hf1, (Hf2, (Hf3, Hf4)))); 
           subst s; right; exists f; 
           exists i; repeat split; auto with datatypes.
         intros H2; case Hf4. 
         unfold lequiv in Hss3; rewrite Hss3; auto.
      -- left; unfold lequiv in Hss3; rewrite Hss3; auto.
      -- case H1; intros f (i, (Hf1, (Hf2, (Hf3, Hf4)))).
         simpl in Hf2; case Hf2; clear Hf2; intros Hf2.
         ++ subst; left; unfold lequiv in Hss3; rewrite Hss3; auto.
            right; exists f; auto.
         ++ generalize (in_states_correct s ss3); 
              case in_states; auto; intros H3.
            right; exists f;
              exists i; repeat split; auto with datatypes.
           rewrite <- Hf3; auto.
    * intros Hl s; case (Hrec ss3 ss4); intros Hr1 Hr2; clear Hrec.
      apply iff_trans with (1 := Hr2 s); clear Hr2.
      split; intros [H1 | H1].
      -- rewrite Hss4 in H1; case H1; auto.
         intros (f, (Hf1, (Hf2, Hf3))); subst s; 
           right; exists f; exists s1; auto with datatypes.
      -- case H1; intros f (i, (Hf1, (Hf2, (Hf3, Hf4)))); subst s; right; exists f; 
           exists i; repeat split; auto with datatypes.
         intros H2; case Hf4.
         unfold lequiv in Hss3; rewrite Hss3; auto.
      -- left; unfold lequiv in Hss4; rewrite Hss4; auto.
      -- match type of H1 with ?X =>
           assert (F1: In s ss1 \/ X); auto
         end.
         rewrite <- Hl, Hr1 in F1; clear Hl Hr1.
         case F1; auto; clear F1; intros F1.
         case H1; intros f (i, (Hf1, (Hf2, (Hf3, Hf4))));
           clear H1; subst s.
         rewrite Hss3 in F1; case F1; clear F1; intros F1.
         ++ case Hf4; auto.
         ++ left; rewrite Hss4; auto.
Qed.

Lemma fold_nexts_equiv ps1 ps2 ss1 ss2 :
  pequiv ps1 ps2 ->
  lequiv ss1 ss2 ->
  pequiv (fold_left nexts (snd ps1) (fst ps1, ss1)) 
         (fold_left nexts (snd ps2) (fst ps2, ss2)).
Proof.
unfold pequiv, lequiv; intros (He1, He2) He3.
case (fold_nexts_correct ps1 ss1); intros Hr1 Hs1.
case (fold_nexts_correct ps2 ss2); intros Hr2 Hs2.
split; intros s.
- apply iff_trans with (1 := Hr1 s).
  apply iff_sym; apply iff_trans with (1 := Hr2 s).
  split; intros [H1 | H1]; auto.
  + left; rewrite He1; auto.
  + right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, Hf4)))).
     exists f; exists i; repeat split; try rewrite He2; try rewrite He1; auto.
  + left; rewrite <- He1; auto.
  + right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, Hf4)))).
    exists f; exists i; repeat split; try rewrite <- He2; 
    try rewrite <- He1; auto.
- apply iff_trans with (1 := Hs1 s).
  apply iff_sym; apply iff_trans with (1 := Hs2 s).
  split; intros [H1 | H1]; auto.
  + left; rewrite He3; auto.
  + right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, Hf4)))).
    exists f; exists i; repeat split; try rewrite He2; try rewrite He1; auto.
  + left; rewrite <- He3; auto.
  + right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, Hf4)))).
    exists f; exists i; repeat split; try rewrite <- He2;
    try rewrite <- He1; auto.
Qed.

Lemma fold_nexts_valid ps ss :
  valid_pair ps ->
  (forall s, In s ss -> valid_state s) ->
  valid_pair  (fold_left nexts (snd ps) (fst ps, ss)).
Proof.
destruct ps as (ss1, ss2); simpl fst; simpl snd.
revert ss1 ss; elim ss2; clear ss2; auto.
- simpl; intros ss1 ss (HH, _) HH1; split; auto.
- intros s ss2 Hrec ss1 ss Hg1 Hg; rewrite fold_left_cons.
  generalize (nexts_valid (ss1, ss) s); case nexts.
  intros ss3 ss4 Hg2.
  case Hg1; simpl fst; simpl snd; intros Hg3 Hg4; 
    case Hg2; auto with datatypes.
  + split; auto.
  + simpl; intros Hg5 Hg6; apply Hrec; auto; split; auto.
    case Hg1; auto with datatypes.
Qed.

Lemma fold_nexts_incl ps ss :
  incl ss (fst ps) ->
  incl (snd (fold_left nexts (snd ps) (fst ps, ss)))
       (fst (fold_left nexts (snd ps) (fst ps, ss))).
Proof.
destruct ps as (ss1, ss2); simpl fst; simpl snd.
revert ss1 ss; elim ss2; clear ss2; auto.
intros s ss2 Hrec ss1 ss H1.
repeat rewrite fold_left_cons.
generalize (nexts_incl (ss1, ss) s); case nexts.
simpl fst; simpl snd.
intros ss3 ss4 H3; apply Hrec; auto with datatypes.
Qed.

Lemma fold_nexts_nreach n ps :
  (forall s, In s (fst ps) <-> nlreachable n s) /\
  (forall s, (nsreachable n s -> In s (snd ps)) /\
             (In s (snd ps) -> nlreachable n s)) ->
  (forall s, In s (fst (fold_left nexts (snd ps) (fst ps,nil)))
                <-> nlreachable (S n) s) /\
  (forall s, (nsreachable (S n) s 
                -> In s (snd (fold_left nexts (snd ps) (fst ps,nil)))) /\
             (In s (snd (fold_left nexts (snd ps) (fst ps,nil)))
                 -> nlreachable (S n) s)).
Proof.
destruct ps as (ss1, ss2).
unfold nexts.
rewrite fold_left_comb with 
  (f := fun (y: state) (y1: state -> state) => y1 y)
  (g := filters).
match goal with |- context[fold_right ?X ?Y ?Z] =>
  change (fold_right X Y Z) with (candidate_list Z)
end; fold filters.
simpl fst; simpl snd.
intros (H1, H2); generalize (filters_correct (ss1, nil) (candidate_list ss2));
 case (fold_left filters  (candidate_list ss2) (ss1, nil)).
intros ss4 ss5; simpl; intros (H3, H4).
assert (tmp: forall (A B: Prop), A -> (A -> B) -> A /\ B); auto.
apply tmp; clear tmp.
- intros s; apply iff_trans with (1:= H3 s).
  split.
  + intros [H5 | H5].
    * case (H1 s); intros HH _.
      case (HH H5); intros m (Hm1, Hm2).
      exists m; auto with arith.
    * assert (H6 := candidate_list_correct ss2 n).
      case (fun x => H6 x s); auto.
  + assert (H6 := candidate_list_correct ss2 n).
    intros H7.
    case (nlreachable_bound _ _ H7); intros m (Hm, Hm1).
    case (le_lt_or_eq _ _ Hm); intros Hm2.
    -- left.
       assert (nlreachable n s).
         apply nlreach_weak with m; auto with arith.
         exists m; split; auto; case Hm1; auto.
       case (H1 s); auto.
    -- subst m; case (fun x => H6 x s); auto.
- intros H5 s; split; intros H6.
  + assert (F0 : In s ss4).
      case (H5 s); auto.
      intros _ H7; apply H7; clear H7.
      exists (S n); split; auto; case H6; auto.
    assert (F1: ~ In s ss1).
      intros H7; case (H1 s); intros H8 _; clear H1.
      generalize (H8 H7); clear H8 H7; intros H7.
      case H7; intros m (Hm1, Hm2); clear H7.
      case H6; intros _ H7.
      case (H7 m); auto with arith.
    case (H4 s); intros _ HH; apply HH; clear HH H4; auto.
    right; split; auto.
    case (H3 s); intros H7 _; auto.
    case H7; auto.
    intros H8; case F1; auto.
   + case (H5 s); intros HH _; apply HH; clear H5 HH.
     case (H3 s); intros _ HH; apply HH; clear H3 HH.
     right; case (H4 s); clear H4.
     intros HH _; case (HH H6); clear HH H6;
       intros HH; case HH; auto.
Qed.

Lemma iters_aux_equiv n ps1 ps2 :
  pequiv ps1 ps2 ->
  pequiv (iters_aux n ps1) (iters_aux n ps2).
Proof.
revert ps1 ps2; elim n; simpl; auto; clear n.
intros n Hrec (sl1, sr1) (sl2, sr2) H1.
apply Hrec.
apply (fold_nexts_equiv (sl1, sr1) (sl2, sr2)); auto.
intros s; split; intros H; case H.
Qed.

Lemma iters_aux_valid n ps :
   valid_pair ps -> valid_pair (iters_aux n ps).
Proof.
revert ps; elim n; simpl; auto; clear n.
intros n Hrec (sl, sr) Hg.
apply Hrec; apply (fold_nexts_valid (sl, sr)); auto.
intros s1 HH; case HH.
Qed.

Lemma iters_aux_incl n ps :
  incl (snd ps) (fst ps) ->
  incl (snd (iters_aux n ps)) (fst (iters_aux n ps)).
Proof.
revert ps; elim n; simpl; auto; clear n.
intros n Hrec (ss1, ss2) Hi; apply Hrec.
apply (fold_nexts_incl (ss1, ss2)); auto with datatypes.
intros z HH; inversion HH.
Qed.

Lemma iters_aux_nreach n m ps :
  (forall s, In s (fst ps) <-> nlreachable m s) /\
  (forall s, (nsreachable m s -> In s (snd ps)) /\
             (In s (snd ps) -> nlreachable m s)) ->
  (forall s, In s (fst (iters_aux n ps)) <-> nlreachable (n + m) s) /\
  (forall s, (nsreachable (n + m) s -> In s (snd (iters_aux n ps))) /\
             (In s (snd (iters_aux n ps)) -> nlreachable (n + m) s)).
Proof.
revert m ps; elim n; simpl; auto; clear n.
intros n Hrec m (ss1, ss2); simpl fst; simpl snd.
replace (S (n + m)) with (n + (S m)); auto with arith.
intros H1; apply Hrec.
apply (fold_nexts_nreach m (ss1, ss2)); auto.
Qed.

Lemma iters_valid n : valid_pair (iters n).
Proof.
unfold iters; apply iters_aux_valid.
split; intros s [H1 | H1]; try (case H1; fail); subst s;
  apply valid_state_init.
Qed.

Lemma iters_incl n : incl (snd (iters n)) (fst (iters n)).
Proof.
unfold iters; apply iters_aux_incl; simpl;
 auto with datatypes.
Qed.

Lemma iters_correct n :
  (forall s, In s (fst (iters n)) <-> nlreachable n s) /\
  (forall s, (nsreachable n s -> In s (snd (iters n))) /\
             (In s (snd (iters n)) -> nlreachable n s)).
Proof.
unfold iters.
pattern n at 2 3 6.
replace n with (n + 0); auto with arith.
apply iters_aux_nreach; simpl.
assert (F1: forall s, nlreachable 0 s -> init_state = s).
- intros s (m, Hm); generalize Hm; case m; clear m Hm.
  + intros (_, HH); inversion HH; auto.
  + intros n1 (Hn1, _); contradict Hn1; auto with arith.
- split; intros s; split; auto.
  + intros [H1 | H1].
    * now subst s; exists 0; split; auto; constructor.
    * now case H1.
  + intros H1; left; apply F1.
    now exists 0; split; auto; case H1; auto.
  + intros [H1 | H1].
    * now subst s; exists 0; split; auto; constructor.
    * now case H1.
Qed.

(* Main theorem if the second list is empty, the first list
   contains all the reachable *)
Lemma iters_final n :
   match iters n with 
   | (_, nil) => forall s, reachable s -> nlreachable (pred n) s
   |    _     => True
   end.
Proof.
generalize (iters_correct n).
case iters; intros s1 s2.
case s2; auto; simpl.
case n; simpl; clear n.
- intros (H1, H2).
  case (H2 init_state); intros HH; case HH.
  split.
  + apply nreach0.
  + intros m Hm; contradict Hm; auto with arith.
- intros n (H1, H2) s Hs.
  elim Hs.
  + exists 0; split; auto with arith.
    now constructor.
  + intros s3 HH1 HH2.
    case (nlreachable_bound (S n) (rright s3)).
    * case HH2; intros m (Hm, Hm1).
      exists (S m); split; auto with arith.
      apply nreachS with s3; auto; unfold move; auto.
    * intros m (Hm, Hm1).
      case (le_lt_or_eq _ _ Hm); intros Hm2.
      -- exists m; split; auto with arith.
         case Hm1; auto.
      -- subst m; case (H2 (rright s3)); intros HH _; case (HH Hm1).
   + intros s3 HH1 HH2.
     case (nlreachable_bound (S n) (rback s3)).
     * case HH2; intros m (Hm, Hm1).
       exists (S m); split; auto with arith.
       apply nreachS with s3; auto; unfold move; auto.
     * intros m (Hm, Hm1).
       case (le_lt_or_eq _ _ Hm); intros Hm2.
       -- exists m; split; auto with arith.
          case Hm1; auto.
       -- subst m; case (H2 (rback s3)); intros HH _; case (HH Hm1).
   + intros s3 HH1 HH2.
     case (nlreachable_bound (S n) (rdown s3)).
     * case HH2; intros m (Hm, Hm1).
       exists (S m); split; auto with arith.
       apply nreachS with s3; auto; unfold move; do 3 right; auto.
     * intros m (Hm, Hm1).
       case (le_lt_or_eq _ _ Hm); intros Hm2.
       exists m; split; auto with arith.
       case Hm1; auto.
       subst m; case (H2 (rdown s3)); intros HH _; case (HH Hm1).
Qed.  

(*****************************************************************************)
(*                                                                           *)
(*            Building the naive solver                                      *)
(*                                                                           *)
(*****************************************************************************)

(* odd for positive *)
Definition is_odd p :=
   match p with xO _ => False | _ => True  end.

(* n % 3 for positive *)
Definition porder n := 
  match (Z_of_nat n mod 3 + 1)%Z with 
    Zpos x => x
  | _  => 1%positive
  end.

(* Same as filters but we split the first list in two to be able
   to do some retrieval *)

Definition filter2s (pmod : positive) (ps : (states * states) * states) (s : state) :=
          let (pstates, nstates) := ps in
          let (states1, states2) := pstates in
          if (in_states s states1 || in_states s states2)%bool
          then ps
          else match pmod with
                 xH => ((s::states1,states2), s::nstates)
               | xO _ => ((states1,s::states2), s::nstates)
               | xI _ => ((s::states1,s::states2), s::nstates)
               end. 

Definition next2s p ps s :=
Eval lazy beta delta [filter2s] in
 fold_left (fun ps f => let s1 := f s in filter2s p ps s1)
   movel ps.

Fixpoint iter2s_aux n p (ps : (states * states) * states) := 
  match n with 
   O => ps 
 | S n1 => let (m,p1) := ps in 
           iter2s_aux n1 (pos_up p) (fold_left (next2s p) p1 (m,nil))
  end.

Definition iter2s n := 
  iter2s_aux n 2%positive (init_state::nil, nil, init_state::nil).

(* An explicit inductive type for moves *)
Inductive moves :=
  Right | Right2 | Rightm1 | Back | Back2 | Backm1 | Down | Down2 | Downm1.

(* Turn a move in an actual rotation *)
Definition m2f m := 
 match m with
  Right => rright 
| Right2 => fun s1 : state => rright (rright s1)
| Rightm1 => fun s1 : state => rright (rright (rright s1))
| Back => rback
| Back2 =>  fun s1 : state => rback (rback s1)
| Backm1  => fun s1 : state => rback (rback (rback s1))
| Down => rdown
| Down2 => fun s1 : state => rdown (rdown s1)           
| Downm1 => fun s1 : state => rdown (rdown (rdown s1))
end.

(* The inverse function *)

Definition minv m := 
 match m with
  Right => Rightm1
| Right2 => Right2
| Rightm1 => Right
| Back => Backm1
| Back2 => Back2
| Backm1  => Back
| Down => Downm1
| Down2 => Down2
| Downm1 => Down
end.

(* The list of all moves *)
Definition Movel := 
  Right :: Right2 :: Rightm1 :: Back :: Back2 :: Backm1 :: 
  Down :: Down2 ::Downm1 :: nil.

(* Compute the number (the reachability index mod 3) of a state *)
Definition get_number s s1 s2 :=
  if in_states s s1 then
    if in_states s s2 then 3%positive else 1%positive
  else
    if in_states s s2 then 2%positive else 4%positive.

(* Find the next state by searching the first neighbour whose
     number decrease modulo *)
Fixpoint get_next_aux n s s1 s2 l :=
  match l with
   nil => None
  | a::l1 => if positive_eq n (get_number (m2f a s) s1 s2) then Some a
             else get_next_aux n s s1 s2 l1
  end.

Definition get_next s s1 s2 := get_next_aux (pos_down (get_number s s1 s2)) s s1 s2 Movel.

(* Now, we just iterate *)

Fixpoint solve n s s1 s2 :=
  match n with
   0 => nil
  | S n1 => match get_next s s1 s2 with
             None => nil
            | Some a => a:: solve n1 (m2f a s) s1 s2
            end
  end.

(*******************************************************************)
(*              Proving iter2s                                     *)
(*******************************************************************)

Definition porder_inv n :
  (porder n = 1 \/ porder n = 2 \/ porder n = 3)%positive.
Proof.
unfold porder.
assert (Ht: (0 < Z_of_nat n mod 3 + 1 < 4)%Z).
  generalize (Z_mod_lt (Z_of_nat n) 3%Z (refl_equal Gt)); auto with zarith.
generalize Ht; case Zplus; auto with zarith; 
 try (intros; discriminate).
do 2 (intros p1; case p1; clear p1; auto);
  intros p1; case p1; try (intros p2 (_, H2); discriminate H2);
  intros (_, H2); discriminate H2.
Qed.

Definition porderS n : porder (S n) = pos_up (porder n).
Proof.
unfold porder, pos_up.
rewrite inj_S; unfold Z.succ; rewrite Zplus_mod.
rewrite <- (Zmod_mod (Z_of_nat n)  3).
rewrite <- Zplus_mod.
generalize (Z_mod_lt (Z_of_nat n) 3%Z (refl_equal Gt)).
case Zmod; simpl; auto.
2: intros p (Hp, _); contradict Hp; auto.
do 3 (intros p; case p; simpl; auto; clear p);
 try (intros p (_, Hp); discriminate Hp).
Qed.

Definition porder_inv1 n : porder n <> 1%positive \/ is_odd (porder n).
Proof.
generalize (porder_inv n); intros [H1 | [H1 | H1]]; rewrite H1; 
  simpl; auto; left; intros HH; discriminate.
Qed.

Definition valid_triple (ps : (states * states) * states) :=
  ((forall s, In s (fst (fst ps)) -> valid_state s) /\
   (forall s, In s (snd (fst ps)) -> valid_state s)) /\
  (forall s, In s (snd ps) -> valid_state s).

Lemma filter2s_valid p ps s1 :
  valid_triple ps -> valid_state s1 -> valid_triple (filter2s p ps s1).
Proof.
destruct ps as ((ss1, ss2), ss3).
intros ((Hg1, Hg2), Hg3) Hg; repeat split;
 intros s; simpl in Hg1, Hg2, Hg3;
   unfold filter2s; case in_states; simpl; auto;
   case in_states; simpl; auto;
   (case p; [intros p1 | intros p1 | idtac]); simpl; auto with datatypes;
   intros [H1 | H1]; auto; subst s1; auto.
Qed.

Lemma filter2s_incl p ps s :
  (forall s1, In s1 (snd ps) -> In s1 (fst (fst ps)) \/ In s1 (snd (fst ps))) ->
  (forall s1, In s1 (snd (filter2s p ps s)) ->
    In s1  (fst (fst (filter2s p ps s))) \/ In s1  (snd (fst (filter2s p ps s)))).
Proof.
destruct ps as ((ss1, ss2), ss3).
intro H; unfold filter2s; intros s1.
do 2 (case in_states; simpl; auto with datatypes); 
  case p; [intros p1 | intros p1 | idtac];
  simpl in H |- *; intros [H1 | H1]; subst; auto;
  case (H _ H1); auto.
Qed.

Lemma filter2s_correct p ps l :
 let ps1 := fold_left (filter2s p) l ps in
 (forall i, In i (fst (fst ps1)) <-> 
    In i (fst (fst ps)) \/
   (~In i (snd (fst ps)) /\ In i l /\ is_odd p)) /\
 (forall i, In i (snd (fst ps1)) <-> 
    In i (snd (fst ps)) \/ 
   (~In i (fst (fst ps)) /\ In i l /\ p <> 1%positive)) /\
 (forall i, In i (snd ps1) <-> In i (snd ps) \/ 
           (~In i (fst (fst ps)) /\ ~In i (snd (fst ps)) /\ In i l)).
Proof.
revert ps; elim l; clear l; simpl; auto.
- intros ps; split; [idtac | split];  intros i; split; auto.
  + intros [HH | (_, (HH, _))]; auto; case HH.
  + intros [HH | (_, (HH, _))]; auto; case HH.
  + intros [HH | (_, (_, HH))]; auto; case HH.
- intros a l Hrec ps.
  case (Hrec (filter2s p ps a)); intros H1 (H2, H3); split; [idtac | idtac].
  + intros i; apply iff_trans with (1 := H1 i).
    unfold filter2s; case ps; simpl; intros ps1; case ps1; 
      intros s1 s2 s3; clear ps ps1 H1 H2 H3.
    generalize (in_states_correct a s1); case in_states; simpl; auto.
    * intros H5; split.
      -- intros [HH | (HH, (HH1, HH2))]; auto.
      -- intros [HH | (HH, ([HH1 | HH1], HH2))]; subst; auto.
    * intros Ha.
      generalize (in_states_correct a s2); case in_states; simpl; auto.
      -- intros Hb; split.
         ++ intros [HH | (HH, (HH1, HH2))]; auto.
         ++ intros [HH | (HH, ([HH1 | HH1], HH2))]; subst; auto.
            case HH; auto.
      -- intros Hb; case p; simpl.
         ++ intros _; split.
            ** intros [[HH | HH]| (HH, (HH1, _))]; subst; auto.
               right; auto.
            ** intros [HH | (HH, ([HH1 | HH1], _))]; subst; auto.
               generalize (state_eq_correct a i); case state_eq; auto.
               intros HH2; right; auto; split; auto.
               intros [HH3 | HH3]; subst; auto.
         ++ intros _; split.
            ** intros [HH | (_, (_, HH))]; auto; case HH.
            ** intros [HH | (_, (_, HH))]; auto; case HH.
         ++ split.
            ** intros [[HH | HH] | (HH, (HH1, _))]; subst; auto.
            ** intros [HH | (HH, ([HH1 | HH1], _))]; auto.
  + split.
    * intros i; apply iff_trans with (1:= H2 i).
      unfold filter2s; case ps; simpl; intros ps1; case ps1; 
        intros s1 s2 s3; clear ps ps1 H1 H2 H3.
      generalize (in_states_correct a s1); case in_states; simpl; auto.
      -- intros H5; split.
         ++ intros [HH | (HH, (HH1, HH2))]; auto.
         ++ intros [HH | (HH, ([HH1 | HH1], HH2))]; subst; auto.
            case HH; auto.
      -- intros Ha.
         generalize (in_states_correct a s2); case in_states; simpl; auto.
         ++ intros Hb; split.
            ** intros [HH | (HH, (HH1, HH2))]; auto.
            ** intros [HH | (HH, ([HH1 | HH1], HH2))]; subst; auto.
         ++ intros Hb; case p; simpl.
            ** intros p1; split.
               --- intros [[HH | HH]| (HH, (HH1, _))]; subst; auto.
                   +++ right; repeat (split; auto); intros HH; discriminate.
                   +++ right; split; auto; split; auto; intros HH2; discriminate.
               --- intros [HH | (HH, ([HH1 | HH1], _))]; subst; auto.
                   generalize (state_eq_correct a i); case state_eq; auto.
                   intros HH2; right; auto; split; auto.
                   +++ intros [HH3 | HH3]; subst; auto.
                   +++ split; auto; intros HH3; discriminate.
            ** intros p1; split.
               --- intros [[HH | HH] | (HH, (HH1, _))]; subst; auto.
                   +++ right; repeat (split; auto); intros HH; discriminate.
                   +++ right; split; auto; split; auto; intros HH2;
                       discriminate.
               --- intros [HH | (HH, ([HH1 | HH1], _))]; auto.
                   right; repeat (split; auto); intros HH2; discriminate.
            ** split.
               --- intros [HH | (_, (_, HH))]; auto; case HH; auto.
               --- intros [HH | (_, (_, HH))]; auto; case HH; auto.
    * intros i; apply iff_trans with (1:= H3 i).
      unfold filter2s; case ps; simpl; intros ps1; case ps1; 
        intros s1 s2 s3; clear ps ps1 H1 H2 H3.
      generalize (in_states_correct a s1); case in_states; simpl; auto.
      -- intros H5; split.
         ++ intros [HH | (HH, (HH1, HH2))]; auto.
         ++ intros [HH | (HH, (HH1, [HH2 | HH2]))]; subst; auto; case HH; auto.
      -- intros Ha.
         generalize (in_states_correct a s2); case in_states; simpl; auto.
         ++ intros Hb; split.
            ** intros [HH | (HH, (HH1, HH2))]; auto.
            ** intros [HH | (HH, (HH1, [HH2 | HH2]))]; subst; auto; case HH1; auto.
         ++ intros Hb; case p; simpl.
            ** intros _; split.
               --- intros [[HH | HH]| (HH, (HH1, HH2))]; subst; auto.
                   right; repeat split; auto.
               --- intros [HH | (HH, (HH1, [HH2 | HH2]))]; auto.
                   generalize (state_eq_correct a i); case state_eq; auto.
                   intros HH3; right; repeat split; auto.
                   +++ intros [HH4 | HH4]; subst; auto.
                   +++ intros [HH4 | HH4]; subst; auto.
            ** intros _; split.
               --- intros [[HH | HH]| (HH, (HH1, HH2))]; subst; auto.
                   right; repeat split; auto.
               --- intros [HH | (HH, (HH1, [HH2 | HH2]))]; auto.
                   generalize (state_eq_correct a i); case state_eq; auto.
                   intros HH3; right; repeat split; auto.
                   intros [HH4 | HH4]; subst; auto.
            ** split.
               --- intros [[HH | HH]| (HH, (HH1, HH2))]; subst; auto.
                   right; repeat split; auto.
               --- intros [HH | (HH, (HH1, [HH2 | HH2]))]; auto.
                   generalize (state_eq_correct a i); case state_eq; auto.
                   intros HH3; right; repeat split; auto.
                   intros [HH4 | HH4]; subst; auto.
Qed.

Definition tequiv {A : Type} (pl1 pl2 : list A * list A * list A) := 
  lequiv (fst (fst pl1)) (fst (fst pl2)) /\ 
  lequiv (snd (fst pl1)) (snd (fst pl2)) /\
  lequiv (snd pl1) (snd pl2).

Lemma filter2s_equiv p ps1 ps2 l1 l2 :
  tequiv ps1 ps2 -> lequiv l1 l2 ->
  tequiv (fold_left (filter2s p) l1 ps1) (fold_left (filter2s p) l2 ps2).
Proof.
intros (H1, (H2, H3)) H4.
case (filter2s_correct p ps1 l1); intros Hr1 (Hs1, Ht1).
case (filter2s_correct p ps2 l2); intros Hr2 (Hs2, Ht2).
unfold lequiv in H1, H2, H3, H4;
  split; [idtac | split]; intros a;
  (rewrite Hr1; rewrite Hr2) ||
  (rewrite Hs1; rewrite Hs2) ||
  (rewrite Ht1; rewrite Ht2).
- split; intros [HH | HH].
  + rewrite <- H1; auto.
  + right; rewrite <- H2, <- H4; auto.
  + rewrite H1; auto.
  + right; rewrite H2, H4; auto.
- split; intros [HH | HH].
  + rewrite <- H2; auto.
  + right; rewrite <- H1, <- H4; auto.
  + rewrite H2; auto.
  + right; rewrite H1, H4; auto.
- split; intros [HH | HH].
  + rewrite <- H3; auto.
  + right; rewrite <- H1, <- H2, <- H4; auto.
  + rewrite H3; auto.
  + right; rewrite H1, H2, H4; auto.
Qed.

Definition next2s_correct p ps s :
 (forall i, In i (fst (fst (next2s p ps s))) <-> 
    In i (fst (fst ps)) \/ exists f, In f movel /\ i = f s /\
    ~In i (snd (fst ps)) /\ is_odd p) /\
 (forall i, In i (snd (fst (next2s p ps s))) <-> 
    In i (snd (fst ps)) \/ exists f, In f movel /\ i = f s /\
    ~In i (fst (fst ps)) /\ p <> 1%positive) /\
 (forall i, In i (snd (next2s p ps s)) <-> 
     In i (snd ps) \/  exists f, In f movel /\ i = f s /\
    ~In i (fst (fst ps)) /\ ~In i (snd (fst ps))).
Proof.
unfold next2s.
match goal with |- context[fold_left ?X _ _] =>
  change X with (fun ps f => let s1 := f s in filter2s p ps s1) 
end.
generalize ps s; elim movel; clear ps s.
- simpl; intros ps s; split; [idtac | split]; intros s1; split; auto; 
    intros HH; case HH; auto;
    case HH; auto; intros (f, (HH1, _)); case HH1.
- intros f lf Hrec ps s; repeat rewrite fold_left_cons.
  split; [idtac | split]; intros s1; case (Hrec (filter2s p ps (f s)) s);
    intros Hr1 (Hr2, Hr3); clear Hrec.
  + apply iff_trans with (1 := Hr1 s1); clear Hr1 Hr2 Hr3.
    unfold filter2s; case ps.
    intros (ss1, ss2) ss3.
    generalize (in_states_correct (f s) ss1); case in_states.
    * simpl fst; auto.
      intros H1; split; intros [H2 | H2]; auto.
      -- case H2; intros f1 (Hf1, (Hf2, (Hf3, Hf4))).
         right; exists f1; auto with datatypes.
      -- case H2; intros f1 (Hf1, (Hf2, (Hf3, Hf4))).
         simpl in Hf1; case Hf1; clear Hf1; intros Hf1.
         ++ left; rewrite Hf2, <- Hf1; auto.
         ++ right; exists f1; auto with datatypes.
    * generalize (in_states_correct (f s) ss2); case in_states.
      -- simpl fst; auto.
         intros H1; split; intros [H2 | H2]; auto.
         ++ case H2; intros f1 (Hf1, (Hf2, (Hf3, Hf4))).
            right; exists f1; auto with datatypes.
         ++ case H2; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); clear H2.
            simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst.
            ** case Hf3; auto.
            ** right; exists f1; auto with datatypes.
      -- case p.
         ++ simpl fst; simpl snd; simpl is_odd.
            intros _ H1 H2; split; intros [H3 | H3]; auto with datatypes.
            ** simpl in H3; case H3; clear H3; intros H3; subst; auto.
               right; exists f; auto with datatypes.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               right; exists f1; repeat split; auto with datatypes.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst; auto with datatypes.
               generalize (state_eq_correct (f s) (f1 s)); case state_eq; intros He.
               --- rewrite He; auto with datatypes.
               --- right; exists f1; repeat split; auto with datatypes.
                   simpl; intros [H3 | H3]; auto.
         ++ simpl fst; simpl snd; simpl is_odd.
            intros _ H1 H2; split; intros [H3 | H3]; auto with datatypes.
            ** case H3; intros f1 (_, (_, (_, HH))); case HH.
            ** case H3; intros f1 (_, (_, (_, HH))); case HH.
         ++ simpl fst; simpl snd; auto.
            intros H1 H2; split; intros [H3 | H3]; auto with datatypes.
            ** simpl in H3; case H3; clear H3; intros H3; subst; auto.
               right; exists f; simpl; auto with datatypes.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               right; exists f1; repeat split; auto with datatypes.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst; auto with datatypes.
               generalize (state_eq_correct (f s) (f1 s)); case state_eq; intros He.
               --- rewrite He; auto with datatypes.
               --- right; exists f1; repeat split; auto with datatypes.
  + apply iff_trans with (1 := Hr2 s1); clear Hr1 Hr2 Hr3.
    unfold filter2s; case ps.
    intros (ss1, ss2) ss3.
    generalize (in_states_correct (f s) ss1); case in_states.
    * simpl fst; simpl snd; auto.
      intros H1; split; intros [H2 | H2]; auto.
      -- case H2; intros f1 (Hf1, (Hf2, (Hf3, Hf4))).
         right; exists f1; auto with datatypes.
      -- case H2; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H2.
         simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst.
         ++ case Hf3; auto.
         ++ right; exists f1; auto with datatypes.
    * simpl fst; simpl snd; auto.
      generalize (in_states_correct (f s) ss2); case in_states;
        simpl fst; simpl snd; auto.
      -- intros H1 H2; split; intros [H3 | H3]; auto with datatypes.
         ++ case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
            right; exists f1; repeat split; auto with datatypes.
         ++ case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
            simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst; auto with datatypes.
            right; exists f1; repeat split; auto with datatypes.
      -- case p; simpl fst; simpl snd; simpl is_odd.
         ++ intros pp H1 H2; split; intros [H3 | H3]; auto with datatypes.
            ** simpl in H3; case H3; clear H3; intros H3; subst; auto.
               right; exists f; repeat split; auto with datatypes; intros HH; discriminate.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               generalize (state_eq_correct (f s) (f1 s)); case state_eq; intros He.
               --- case Hf3; simpl; auto with datatypes.
               --- right; exists f1; repeat split; auto with datatypes.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst; auto with datatypes.
               generalize (state_eq_correct (f1 s) (f s)); case state_eq; intros He;
                 auto with datatypes.
               --- left; simpl; auto with datatypes.
               --- right; exists f1; repeat split; auto with datatypes.
                   simpl; intros [H3 | H3]; auto.
         ++ intros pp H1 H2; split; intros [H3 | H3]; auto with datatypes.
            ** simpl in H3; case H3; clear H3; intros H3; subst; auto with datatypes.
               right; exists f; repeat split; auto with datatypes; intros HH; 
               discriminate HH.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               right; exists f1; repeat split; auto with datatypes.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               generalize (state_eq_correct (f s) (f1 s)); case state_eq; intros He.
               --- simpl; rewrite He; auto.
               --- simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst; auto with datatypes.
                   right; exists f1; repeat split; auto with datatypes.
         ++ intros H1 H2; split; intros [H3 | H3]; auto with datatypes.
            ** case H3; intros f1 (_, (_, (_, HH))); case HH; auto.
            ** case H3; intros f1 (_, (_, (_, HH))); case HH; auto.
  + apply iff_trans with (1 := Hr3 s1); clear Hr1 Hr2 Hr3.
    * unfold filter2s; case ps.
      intros (ss1, ss2) ss3.
      generalize (in_states_correct (f s) ss1); case in_states;
        simpl fst; simpl snd; auto.
      -- intros H1; split; intros [H2 | H2]; auto.
         ++ case H2; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; auto; clear H2.
            right; exists f1; auto with datatypes.
         ++ case H2; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H2.
            simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst.
            ** case Hf3; auto.
            ** right; exists f1; auto with datatypes.
      -- generalize (in_states_correct (f s) ss2); case in_states;
           simpl fst; simpl snd; auto.
         ++ intros H1 H2; split; intros [H3 | H3]; auto with datatypes.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               right; exists f1; repeat split; auto with datatypes.
            ** case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
               simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst; auto with datatypes.
               --- case Hf4; auto.
               --- right; exists f1; repeat split; auto with datatypes.
         ++ case p; simpl fst; simpl snd; auto.
            ** intros _ H1 H2; split; intros [H3 | H3]; auto with datatypes.
               --- simpl in H3; case H3; clear H3; intros H3; subst; auto.
                   right; exists f; auto with datatypes.
               --- case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
                   generalize (state_eq_correct (f s) (f1 s)); case state_eq; intros He.
                   +++ case Hf3; simpl; auto with datatypes.
                   +++ right; exists f1; repeat split; auto with datatypes.
               --- case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
                   simpl in Hf1; case Hf1; clear Hf1; intros Hf1; subst; auto with datatypes.
                   generalize (state_eq_correct (f1 s) (f s)); case state_eq; intros He;
                     auto with datatypes.
                   +++ left; simpl; auto with datatypes.
                   +++ right; exists f1; repeat split; auto with datatypes.
                       *** simpl; intros [H3 | H3]; auto.
                       *** simpl; intros [H3 | H3]; auto.
            ** intros _ H1 H2; split; intros [H3 | H3]; auto with datatypes.
               --- simpl in H3; case H3; clear H3; intros H3; subst; auto.
                   right; exists f; auto with datatypes.
               --- case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
                   right; exists f1; repeat split; auto with datatypes.
               --- case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
                   generalize (state_eq_correct (f s) (f1 s)); case state_eq; 
                   intros He.
                   +++ simpl; rewrite He; auto.
                   +++ simpl in Hf1; case Hf1; clear Hf1; 
                         intros Hf1; subst; auto with datatypes.
                       right; exists f1; repeat split; auto with datatypes.
                       simpl; intros [H3 | H3]; auto.
            ** intros H1 H2; split; intros [H3 | H3]; auto with datatypes.
               --- simpl in H3; case H3; clear H3; intros H3; subst; auto.
                   right; exists f; auto with datatypes.
               --- case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
                   right; exists f1; repeat split; auto with datatypes.
               --- case H3; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); subst; clear H3.
                   generalize (state_eq_correct (f s) (f1 s));
                   case state_eq; intros He.
                   +++ simpl; rewrite He; auto.
                   +++ simpl in Hf1; case Hf1; clear Hf1; intros Hf1;
                         subst; auto with datatypes.
                       right; exists f1; repeat split; auto with datatypes.
                       simpl; intros [H3 | H3]; auto.
Qed.

Lemma next2s_equiv p ps1 ps2 s :
  tequiv ps1 ps2 -> tequiv (next2s p ps1 s) (next2s p ps2 s).
Proof.
intros (H1, (H2, H3)).
case (next2s_correct p ps1 s); intros Hr1 (Hs1, Ht1).
case (next2s_correct p ps2 s); intros Hr2 (Hs2, Ht2).
split; [idtac | split]; intros a.
- apply iff_trans with (1:= (Hr1 a)); clear Hr1 Hs1 Ht1.
  apply iff_sym; apply iff_trans with (1:= (Hr2 a)); clear Hr2 Hs2 Ht2.
  split; intros [H4 | H4].
  + left; case (H1 a); auto.
  + case H4; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); right; exists f1;
    repeat split; auto; subst; case (H2 (f1 s)); auto.
  + left; case (H1 a); auto.
  + case H4; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); right; exists f1;
    repeat split; auto; subst; case (H2 (f1 s)); auto.
- apply iff_trans with (1:= (Hs1 a)); clear Hr1 Hs1 Ht1.
  apply iff_sym; apply iff_trans with (1:= (Hs2 a)); clear Hr2 Hs2 Ht2.
  split; intros [H4 | H4].
  + left; case (H2 a); auto.
  + case H4; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); right; exists f1;
    repeat split; auto; subst; case (H1 (f1 s)); auto.
  + left; case (H2 a); auto.
  + case H4; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); right; exists f1;
    repeat split; auto; subst; case (H1 (f1 s)); auto.
- apply iff_trans with (1:= (Ht1 a)); clear Hr1 Hs1 Ht1.
  apply iff_sym; apply iff_trans with (1:= (Ht2 a)); clear Hr2 Hs2 Ht2.
  split; intros [H4 | H4].
  + left; case (H3 a); auto.
  + case H4; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); right; exists f1;
    repeat split; auto; subst; case (H1 (f1 s));
    case (H2 (f1 s)); auto.
  + left; case (H3 a); auto.
  + case H4; intros f1 (Hf1, (Hf2, (Hf3, Hf4))); right; exists f1;
    repeat split; auto; subst; case (H1 (f1 s));
    case (H2 (f1 s)); auto.
Qed.

Lemma next2s_valid p ps s :
  valid_triple ps -> valid_state s -> valid_triple (next2s p ps s).
Proof.
unfold next2s.
match goal with |- context[fold_left ?X _ _] =>
  change X with (fun ps f => let s1 := f s in filter2s p ps s1) 
end.
generalize ps s (movel_valid); elim movel; auto; clear ps s.
intros f lf Hrec ps s1 Hf Hg1 Hg; rewrite fold_left_cons.
apply Hrec; auto with datatypes.
generalize (filter2s_valid p ps (f s1) Hg1); auto with datatypes.
Qed.

Lemma next2s_incl p ps s :
  (forall s1, In s1 (snd ps) -> In s1 (fst (fst ps)) \/ In s1 (snd (fst ps))) ->
  (forall s1, In s1 (snd (next2s p ps s)) ->
    In s1  (fst (fst (next2s p ps s))) \/ In s1  (snd (fst (next2s p ps s)))).
Proof.
unfold next2s.
match goal with |- context[fold_left ?X _ _] =>
  change X with (fun ps f => let s1 := f s in filter2s p ps s1) 
end.
generalize ps s; elim movel; auto; clear ps s.
intros f lf Hrec ps s Hs; repeat rewrite fold_left_cons.
generalize (filter2s_incl p ps (f s)).
lazy zeta.
case filter2s; intros (ss3, ss4) ss5 Hss3.
apply Hrec; auto with datatypes; clear Hrec.
Qed.

Lemma fold_next2s_correct p ps ss :
 (forall i, In i (fst (fst (fold_left (next2s p) (snd ps) (fst ps, ss)))) <-> 
    In i (fst (fst ps)) \/ exists f, exists s, In f movel /\ In s (snd ps) /\ i = f s /\
    ~In i (snd (fst ps)) /\ is_odd p) /\
 (forall i, In i (snd (fst (fold_left (next2s p) (snd ps) (fst ps, ss)))) <-> 
    In i (snd (fst ps)) \/ exists f, exists s, In f movel /\ In s (snd ps) /\ i = f s /\
    ~In i (fst (fst ps)) /\ p <> 1%positive) /\
 (forall i, In i (snd (fold_left (next2s p) (snd ps) (fst ps, ss))) <-> 
     In i ss \/  exists f, exists s, In f movel /\ In s (snd ps) /\ i = f s /\
    ~In i (fst (fst ps)) /\ ~In i (snd (fst ps))).
Proof.
destruct ps as (ss1, ss2); simpl fst; simpl snd.
generalize ss1 ss; elim ss2; clear ss ss1 ss2; auto.
- unfold fold_left, fst, snd.
  intros ss1 ss; split; [idtac | split]; intros;
     split; auto.
  + intros [H1 | H1]; auto.
    case H1; intros f (i1, (_, (HH, _))); case HH.
  + intros [H1 | H1]; auto.
    case H1; intros f (i1, (_, (HH, _))); case HH.
  + intros [H1 | H1]; auto.
    case H1; intros f (i1, (_, (HH, _))); case HH.
- intros s1 ss2 Hrec ss1 ss.
  rewrite fold_left_cons.
  generalize (next2s_correct p (ss1, ss) s1); case next2s; 
    simpl fst; simpl snd; intros (ss3, ss4) ss5 (Hss3, (Hss4, Hss5)).
  simpl fst in Hss3, Hss4, Hss5; simpl snd in Hss3, Hss4, Hss5.
  split; [idtac | split].
  + intros s; case (Hrec (ss3, ss4) ss5); intros Hr1 (Hr2, Hr3); clear Hrec.
    apply iff_trans with (1 := Hr1 s); simpl fst; simpl snd; clear Hr1 Hr2 Hr3.
    split; intros [H1 | H1].
    * rewrite Hss3 in H1; case H1; auto.
      intros (f, (Hf1, (Hf2, Hf3))); subst s; right; exists f; exists s1; 
      auto with datatypes.
    * case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))); subst s; 
        right; exists f; 
        exists i; repeat split; auto with datatypes.
      intros H2; case Hf4.
      rewrite Hss4; auto.
    * left; unfold lequiv in Hss3; rewrite Hss3; auto.
    * case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))); subst; 
        auto; clear H1.
      simpl in Hf2; case Hf2; clear Hf2; intros Hf2; subst; auto.
      -- left; rewrite Hss3; auto.
         right; exists f; auto.
      -- generalize (in_states_correct (f i) ss3); case in_states; auto; intros H3.
         right; exists f; exists i; repeat split; auto.
         rewrite Hss4.
         intros [HH | HH]; auto.
         case H3; rewrite Hss3; auto.
         case HH; intros f1 (Gf1, (Gf2, (Gf3, Gf4))).
         right; exists f1; split; auto.
  + intros s; case (Hrec (ss3, ss4) ss5); intros Hr1 (Hr2, Hr3); clear Hrec.
    apply iff_trans with (1 := Hr2 s); simpl fst; simpl snd; clear Hr1 Hr2 Hr3.
    split; intros [H1 | H1].
    * rewrite Hss4 in H1; case H1; auto.
      intros (f, (Hf1, (Hf2, Hf3))); subst s; right; exists f; exists s1; 
        auto with datatypes.
    * case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))); subst s; right;
        exists f; exists i; repeat split; auto with datatypes.
      intros H2; case Hf4.
      rewrite Hss3; auto.
    * left; rewrite Hss4; auto.
    * case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))); subst; 
        auto; clear H1.
      simpl in Hf2; case Hf2; clear Hf2; intros Hf2; subst; auto.
      -- left; rewrite Hss4; auto.
         right; exists f; auto.
      -- generalize (in_states_correct (f i) ss4); case in_states; 
           auto; intros H3.
         right; exists f; exists i; repeat split; auto.
         rewrite Hss3.
         intros [HH | HH]; auto.
         case H3; rewrite Hss4; auto.
         case HH; intros f1 (Gf1, (Gf2, (Gf3, Gf4))).
         right; exists f1; split; auto.
  + intros s; case (Hrec (ss3, ss4) ss5); intros Hr1 (Hr2, Hr3); clear Hrec.
    apply iff_trans with (1 := Hr3 s); simpl fst; simpl snd; clear Hr1 Hr2 Hr3.
    split; intros [H1 | H1].
    * rewrite Hss5 in H1; case H1; auto.
      intros (f, (Hf1, (Hf2, Hf3))); subst s; right; exists f; exists s1; 
        auto with datatypes.
    * case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))); subst s; 
        right; exists f; 
        exists i; repeat split; auto with datatypes.
      -- intros H2; case Hf4.
         rewrite Hss3; auto.
      -- intros H2; case Hf5.
         rewrite Hss4; auto.
    * left; rewrite Hss5; auto.
    * case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))); subst; 
         auto; clear H1.
      simpl in Hf2; case Hf2; clear Hf2; intros Hf2; subst; auto.
      -- left; rewrite Hss5; auto.
         right; exists f; auto.
      -- generalize (in_states_correct (f i) ss5); case in_states; 
           auto; intros H3.
         right; exists f; exists i; repeat split; auto.
         ++ rewrite Hss3.
            intros [HH | HH]; auto.
            case H3; rewrite Hss5; auto; clear H3.
            case HH; intros f1 (Gf1, (Gf2, (Gf3, Gf4))).
            right; exists f1; split; auto.
         ++ rewrite Hss4; intros [HH | HH].
            ** case Hf5; auto.
            ** case HH; intros f1 (Gf1, (Gf2, (Gf3, Gf4))).
               case H3; rewrite Hss5.
               right; exists f1; auto.
Qed.

Lemma fold_next2s_equiv p ps1 ps2 ss1 ss2 :
  tequiv ps1 ps2 ->
  lequiv ss1 ss2 ->
  tequiv (fold_left (next2s p) (snd ps1) (fst ps1, ss1)) 
         (fold_left (next2s p) (snd ps2) (fst ps2, ss2)).
Proof.
unfold tequiv, lequiv.
 intros (He1, (He2, He3)) He4.
case (fold_next2s_correct p ps1 ss1); intros Hr1 (Hs1, Ht1).
case (fold_next2s_correct p ps2 ss2); intros Hr2 (Hs2, Ht2).
split; [idtac | split]; intros s.
apply iff_trans with (1 := Hr1 s); clear Hr1 Hs1 Ht1.
apply iff_sym; apply iff_trans with (1 := Hr2 s); clear Hr2 Hs2 Ht2.
split; intros [H1 | H1]; auto.
left; rewrite He1; auto.
right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))).
exists f; exists i; repeat split; try rewrite He2; try rewrite He1; auto.
rewrite He3; auto.
left; rewrite <- He1; auto.
right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))).
exists f; exists i; repeat split; try rewrite <- He2; try rewrite <- He1; auto.
rewrite <- He3; auto.
apply iff_trans with (1 := Hs1 s); clear Hr1 Hs1 Ht1.
apply iff_sym; apply iff_trans with (1 := Hs2 s); clear Hr2 Hs2 Ht2.
split; intros [H1 | H1]; auto.
left; rewrite He2; auto.
right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))).
exists f; exists i; repeat split; try rewrite He2; try rewrite He1; auto.
rewrite He3; auto.
left; rewrite <- He2; auto.
right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))).
exists f; exists i; repeat split; try rewrite <- He2; try rewrite <- He1; auto.
rewrite <- He3; auto.
apply iff_trans with (1 := Ht1 s); clear Hr1 Hs1 Ht1.
apply iff_sym; apply iff_trans with (1 := Ht2 s); clear Hr2 Hs2 Ht2.
split; intros [H1 | H1]; auto.
left; rewrite He4; auto.
right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))).
exists f; exists i; repeat split; try rewrite He2; try rewrite He1; auto.
rewrite He3; auto.
left; rewrite <- He4; auto.
right; case H1; intros f (i, (Hf1, (Hf2, (Hf3, (Hf4, Hf5))))).
exists f; exists i; repeat split; try rewrite <- He2; try rewrite <- He1; auto.
rewrite <- He3; auto.
Qed.

Lemma fold_next2s_valid p ps ss :
  valid_triple ps ->
  (forall s, In s ss -> valid_state s) ->
  valid_triple (fold_left (next2s p) (snd ps) (fst ps, ss)).
Proof.
destruct ps as (ss1, ss2); simpl fst; simpl snd.
revert ss1 ss; elim ss2; clear ss2; auto.
- simpl; intros ss1 ss (HH, _) HH1; split; auto.
- intros s ss2 Hrec ss1 ss Hg1 Hg; rewrite fold_left_cons.
  generalize (next2s_valid p (ss1, ss) s); case next2s.
  intros ss3 ss4 Hg2.
  case Hg1; simpl fst; simpl snd; intros Hg3 Hg4; case Hg2;
  auto with datatypes.
  + split; auto.
  + simpl; intros Hg5 Hg6; apply Hrec; auto; split; auto.
    case Hg1; auto with datatypes.
Qed.

Lemma fold_next2s_incl p ps ss :
  (forall s1, In s1 ss -> In s1 (fst (fst ps)) \/ In s1 (snd (fst ps))) ->
  (forall s1, In s1 (snd (fold_left (next2s p) (snd ps) (fst ps, ss))) ->
    In s1  (fst (fst (fold_left (next2s p) (snd ps) (fst ps, ss)))) \/ 
    In s1  (snd (fst (fold_left (next2s p) (snd ps) (fst ps, ss))))).
Proof.
destruct ps as (ss1, ss2); simpl fst; simpl snd.
revert ss1 ss; elim ss2; clear ss2; auto.
intros s ss2 Hrec ss1 ss H1.
repeat rewrite fold_left_cons.
generalize (next2s_incl p (ss1, ss) s); case next2s.
simpl fst; simpl snd.
intros ss3 ss4 H3; apply Hrec; auto with datatypes.
Qed.

Lemma fold_next2s_nreach n p ps :
   p = porder (S n) ->
  (forall s, In s (fst (fst ps)) <-> 
     exists m, m <= n /\ nsreachable m s /\ is_odd (porder m)) /\
  (forall s, In s (snd (fst ps)) <-> 
     exists m, m <= n /\  nsreachable m s /\ porder m <> 1%positive) /\
  (forall s, (nsreachable n s -> In s (snd ps)) /\
             (In s (snd ps) -> nlreachable n s)) ->
  (forall s, In s (fst (fst (fold_left (next2s p) (snd ps) (fst ps,nil)))) <-> 
     exists m, m <= S n /\ nsreachable m s /\ is_odd (porder m)) /\
  (forall s, In s  (snd (fst (fold_left (next2s p) (snd ps) (fst ps,nil)))) <-> 
     exists m, m <= S n /\ nsreachable m s /\ porder m <> 1%positive) /\
  (forall s, (nsreachable (S n) s 
                -> In s (snd (fold_left (next2s p) (snd ps) (fst ps,nil)))) /\
             (In s (snd (fold_left (next2s p) (snd ps) (fst ps,nil)))
                 -> nlreachable (S n) s)).
Proof.
destruct ps as (ss1, ss2).
unfold next2s.
rewrite fold_left_comb with 
  (f := fun (y: state) (y1: state -> state) => y1 y)
  (g := filter2s p).
match goal with |- context[fold_right ?X ?Y ?Z] =>
  change (fold_right X Y Z) with (candidate_list Z)
end; fold filters.
simpl fst; simpl snd.
intros Hn (H1, (H2, H3)); generalize (filter2s_correct p (ss1, nil) (candidate_list ss2));
 case (fold_left (filter2s p) (candidate_list ss2) (ss1, nil)).
intros ss4 ss5; simpl; intros (H4, (H5, H6)).
split; [idtac | split].
- intros s; apply iff_trans with (1:= H4 s).
  split.
  + generalize (in_states_correct s (fst ss1)); case in_states; intros He.
    * intros _; case (H1 s); intros HH _.
      case (HH He); intros m (Hm1, (Hm2, Hm3)).
      exists m; repeat (split; auto with arith).
    * intros [H7 | (H8, (H9, H10))].
      -- case He; auto.
      -- assert (H11 := candidate_list_correct ss2 n).
           case (fun x => H11 x s); auto.
         intros _ H12; generalize (H12 H9); clear H11 H12; intros H11.
         case (nlreachable_bound _ _ H11); intros m (Hm, Hm1).
         case (le_lt_or_eq _ _ Hm); intros Hm2.
         ++ case (porder_inv1 m); intros Hm3.
            ** case H8; rewrite H2; exists m; auto with arith.
            ** case He; rewrite H1; exists m; auto with arith.
         ++ subst; exists (S n); repeat (split; auto).
  + rewrite Hn; auto.
    intros (m, (Hm1, (Hm2, Hm3))).
    case (le_lt_or_eq _ _ Hm1); clear Hm1; intros Hm1.
    * left.
      rewrite H1; exists m; auto with arith.
    * subst; right; split; auto.
      -- rewrite H2.
         intros (m1, (Hm4, (Hm5, Hmm6))).
         contradict Hm4.
         rewrite (nsreachable_unique _ _ _ Hm5 Hm2); auto with arith.
      -- split; auto.
         assert (H11 := candidate_list_correct ss2 n).
         case (fun x => H11 x s); auto.
- intros s; apply iff_trans with (1:= H5 s).
  split.
  + generalize (in_states_correct s (snd ss1)); case in_states; intros He.
    * intros _; case (H2 s); intros HH _.
      case (HH He); intros m (Hm1, (Hm2, Hm3)).
      exists m; repeat (split; auto with arith).
    * intros [H7 | (H8, (H9, H10))].
      -- case He; auto.
      -- assert (H11 := candidate_list_correct ss2 n).
         case (fun x => H11 x s); auto.
         intros _ H12; generalize (H12 H9); clear H11 H12; intros H11.
         case (nlreachable_bound _ _ H11); intros m (Hm, Hm1).
         case (le_lt_or_eq _ _ Hm); intros Hm2.
         ++ case (porder_inv1 m); intros Hm3.
            ** case He; rewrite H2; exists m; auto with arith.
            ** case H8; rewrite H1; exists m; auto with arith.
         ++ subst; exists (S n); repeat (split; auto).
  + rewrite Hn; auto.
    intros (m, (Hm1, (Hm2, Hm3))).
    case (le_lt_or_eq _ _ Hm1); clear Hm1; intros Hm1.
    * left.
      rewrite H2; exists m; auto with arith.
    * subst; right; split; auto.
      -- rewrite H1.
         intros (m1, (Hm4, (Hm5, Hmm6))).
         contradict Hm4; rewrite (nsreachable_unique _ _ _ Hm5 Hm2); 
           auto with zarith.
      -- split; auto.
         assert (H11 := candidate_list_correct ss2 n).
         case (fun x => H11 x s); auto.
- intros s; split; rewrite H6; intros Hg.
  + right; split; [idtac | split]; auto.
    * rewrite H1; intros (m, (Hm, (Hm1, _))).
      case Hg; intros _ HH; case (HH m); auto with arith.
      case Hm1; auto.
    * rewrite H2; intros (m, (Hm, (Hm1, _))).
      case Hg; intros _ HH; case (HH m); auto with arith.
      case Hm1; auto.
    * case (fun x => candidate_list_correct ss2 n x s); auto.
  + case Hg; [intros HH; case HH | intros (G1, (G2, G3))].
    case (fun x => candidate_list_correct ss2 n x s); auto.
Qed.

Lemma iter2s_aux_equiv n p ps1 ps2 :
  tequiv ps1 ps2 ->
  tequiv (iter2s_aux n p ps1) (iter2s_aux n p ps2).
Proof.
revert p ps1 ps2; elim n; simpl; auto; clear n.
intros n Hrec p (sl1, sr1) (sl2, sr2) H1.
apply Hrec.
apply (fold_next2s_equiv p (sl1, sr1) (sl2, sr2)); auto.
intros s; split; intros H; case H.
Qed.

Lemma iter2s_aux_valid n p ps :
   valid_triple ps -> valid_triple (iter2s_aux n p ps).
Proof.
revert p ps; elim n; simpl; auto; clear n.
intros n Hrec p (sl, sr) Hg.
apply Hrec; apply (fold_next2s_valid p (sl, sr)); auto.
intros s1 HH; case HH.
Qed.

Lemma iter2s_aux_incl n p ps :
  (forall s1, In s1 (snd ps) -> In s1 (fst (fst ps)) \/ In s1 (snd (fst ps))) ->
  (forall s1, In s1 (snd  (iter2s_aux n p ps))  ->
    In s1  (fst (fst (iter2s_aux n p ps))) \/ In s1  (snd (fst (iter2s_aux n p ps)))).
Proof.
revert p ps; elim n; simpl; auto; clear n.
intros n Hrec p (ss1, ss2) Hi; apply Hrec.
apply (fold_next2s_incl p (ss1, ss2)); auto with datatypes.
intros z HH; inversion HH.
Qed.

Lemma iter2s_aux_nreach n p m ps :
   p = porder (S m) ->
  (forall s, In s (fst (fst ps)) <-> 
     exists m1, m1 <= m /\ nsreachable m1 s /\ is_odd (porder m1)) /\
  (forall s, In s (snd (fst ps)) <-> 
     exists m1, m1 <= m /\  nsreachable m1 s /\ porder m1 <> 1%positive) /\
  (forall s, (nsreachable m s -> In s (snd ps)) /\
             (In s (snd ps) -> nlreachable m s)) ->
  (forall s, In s (fst (fst (iter2s_aux n p ps))) <-> 
     exists m1, m1 <= n + m /\ nsreachable m1 s /\ is_odd (porder m1)) /\
  (forall s, In s  (snd (fst (iter2s_aux n p ps))) <-> 
     exists m1, m1 <= n + m /\ nsreachable m1 s /\ porder m1 <> 1%positive) /\
  (forall s, (nsreachable (n + m) s 
                -> In s (snd (iter2s_aux n p ps))) /\
             (In s (snd (iter2s_aux n p ps))
                 -> nlreachable (n + m) s)).
Proof.
revert p m ps; elim n; auto; clear n.
intros n Hrec p m (ss1, ss2); simpl fst; simpl snd.
rewrite plus_Snm_nSm.
intros H1 (H2, (H3, H4)); apply (Hrec (pos_up p) (S m)).
rewrite H1; repeat rewrite porderS; auto.
apply (fold_next2s_nreach m p (ss1, ss2)); auto.
Qed.

Lemma iter2s_valid n : valid_triple (iter2s n).
Proof.
unfold iter2s; apply iter2s_aux_valid.
repeat split; simpl; try (intros s HH; case HH; fail);
  intros s [H1 | H1]; try (case H1; fail); subst s;
  apply valid_state_init.
Qed.

Lemma iter2s_incl n :
  (forall s1, In s1 (snd  (iter2s n))  ->
    In s1  (fst (fst (iter2s n))) \/ In s1  (snd (fst (iter2s n)))).
Proof.
unfold iter2s; apply iter2s_aux_incl; simpl;
 auto with datatypes.
Qed.

Lemma iter2s_correct n :
  (forall s, In s (fst (fst (iter2s n))) <-> 
     exists m1, m1 <= n /\ nsreachable m1 s /\ is_odd (porder m1)) /\
  (forall s, In s  (snd (fst (iter2s n))) <-> 
     exists m1, m1 <= n /\ nsreachable m1 s /\ porder m1 <> 1%positive) /\
  (forall s, (nsreachable n s 
                -> In s (snd (iter2s n))) /\
             (In s (snd (iter2s n))
                 -> nlreachable n s)).
Proof.
unfold iters.
pattern n at 2 4 5 8.
replace n with (n + 0); auto with arith.
unfold iter2s; apply iter2s_aux_nreach; simpl; auto.
assert (F1: forall s, nsreachable 0 s -> init_state = s).
- intros s (H1, H2); inversion H1; auto.
- split.
  + intros s; split; auto.
    intros [H1 | H1].
    * subst; exists 0; repeat split; auto; try constructor.
      now intros m Hm; contradict Hm; auto with arith.
    * case H1; auto.
    * intros (m1, (Hm1, (Hm2, _))); left.
      apply F1; generalize Hm1 Hm2; case m1; simpl; auto.
      intros n1 Hn1; contradict Hn1; auto with arith.
  + split.
    * intros s; split; auto.
      intros HH; case HH.
      intros (m1, (Hm1, (Hm2, Hm3))).
      generalize Hm1 Hm3; case m1; simpl; auto.
      intros n1 Hn1; contradict Hn1; auto with arith.
    * intros s; split; auto.
      intros [HH | HH]; subst; try (case HH; fail).
      exists 0; split; auto; constructor.
Qed.

(* Main theorem, as before (s1,s2) contains all the reachable
   states *)

Lemma iter2s_final n :
  let (ss1, s3) := iter2s n in
   let (s1, s2) := ss1 in
   match s3 with 
    nil => 
  (forall s, reachable s -> In s s1 \/ In s s2) /\
  (forall s, In s s1 -> 
     exists m1, m1 <= n /\ nsreachable m1 s /\ is_odd (porder m1)) /\
  (forall s, In s  s2 -> 
     exists m1, m1 <= n /\ nsreachable m1 s /\ porder m1 <> 1%positive)
  | _ => True
   end.
Proof.
generalize (iter2s_correct n).
case iter2s; intros (s1, s2) s3.
case s3; auto; simpl.
intros (H1, (H2, H3)).
split; auto.
- intros s Hs.
  case (reachable_nreachable _ Hs).
  intros k Hk.
  case (nsreachable_bound _ _ Hk).
  intros m (Hm, Hm1).
  case (le_or_lt m n); intros Hn.
  + case (porder_inv1 m); intros H4.
    * right; rewrite H2; exists m; auto.
    * left; rewrite H1; exists m; auto.
  + case (nsreachable_inv n m s); auto with arith.
    intros s4 Hs3; case (H3 s4).
    intros HH; case (HH Hs3); auto.
- split; auto.
  + intros s; case (H1 s); auto.
  + intros s; case (H2 s); auto.
Qed.

(*****************************************************************************)
(*              Proving the solver                                           *)
(*****************************************************************************)


Lemma move_map: movel = map m2f Movel.
Proof. apply refl_equal. Qed.

Lemma moves_inv m s : valid_state s -> s = m2f (minv m) (m2f m s).
Proof.
case m; case s; unfold valid_state; simpl; intuition;
repeat rewrite oup_down; repeat rewrite odown_up; auto.
Qed.

Lemma get_number_correct n n1 s s1 s2 :
  (s1, s2) = fst (iter2s n) -> n1 <= n ->
  nsreachable n1 s ->  porder n1 = get_number s s1 s2.
Proof.
generalize (iter2s_correct n); case iter2s.
intros (s3, s4) ss; simpl; intros (H1, (H2, H3)) HH Hl Hr.
injection HH; intros; subst s3 s4; clear HH.
unfold get_number.
generalize (in_states_correct s s1); case in_states.
- rewrite H1; intros (m, (Hm, (Hm1, Hm2))).
  assert(m = n1); subst.
    apply nsreachable_unique with s; auto.
  generalize (in_states_correct s s2); case in_states.
  + rewrite H2; intros (m1, (Hm3, (Hm4, Hm5))).
    assert (m1 = n1); subst.
      apply nsreachable_unique with s; auto.
    generalize Hm2 Hm5; generalize (porder_inv n1); 
      intros [HH | [HH | HH]]; rewrite HH; auto.
    * intros _ HH1; case HH1; auto.
    * intros HH1; case HH1.
  + intros HH; generalize (positive_eq_correct (porder n1) 1);
      case positive_eq; auto; intros HH1.
    case HH; rewrite H2; exists n1; auto.
- generalize (in_states_correct s s2); case in_states.
  + intros _ HH; generalize (porder_inv n1); 
      intros [HH1 | [HH1 | HH1]]; rewrite HH1; auto.
    * case HH; rewrite H1; exists n1; rewrite HH1; simpl; auto.
    * case HH; rewrite H1; exists n1; rewrite HH1; simpl; auto.
  + intros HH HH1; generalize (porder_inv1 n1); intros [HH2 | HH2].
    * case HH; rewrite H2; exists n1; auto.
    * case HH1; rewrite H1; exists n1; auto.
Qed.

Lemma get_next_aux_correct n s s1 s2 l :
  match get_next_aux n s s1 s2 l with 
    Some a => 
   In a l /\ get_number (m2f a s) s1 s2 = n
  | None => 
      forall a, In  a l -> get_number (m2f a s) s1 s2 <> n
  end.
Proof.
elim l; simpl; auto.
intros a l1 Hrec; generalize (positive_eq_correct n (get_number (m2f a s) s1 s2));
  case positive_eq; try (intros; discriminate); auto.
generalize Hrec; case get_next_aux; auto.
- intros m1 (H1, H2) H3; auto.
- intros H1 H2 a1 [H3 | H3]; subst; auto.
Qed.

Lemma move_Movel s s1 :
  move s s1 -> exists a, In a Movel /\ s1 = m2f a s.
Proof.
intros [H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|H1]]]]]]]]; subst.
- exists Right; simpl; split; auto.
- exists Right2; simpl; split; auto.
- exists Rightm1; simpl; split; auto.
- exists Back; simpl; split; auto.
- exists Back2; simpl; split; auto; right; auto.
- exists Backm1; simpl; split; auto; do 2 right; auto.
- exists Down; simpl; split; auto; do 3 right; auto.
- exists Down2; simpl; split; auto; do 4 right; auto.
- exists Downm1; simpl; split; auto; do 5 right; auto.
Qed.

Lemma Movel_move s a : In a Movel -> move s (m2f a s).
Proof.
simpl; intros [H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|H1]]]]]]]]]; subst;
  simpl; red; auto; do 3 right; auto; do 3 right; auto.
case H1.
Qed.

Lemma porder_move s1 s2 n1 n2 : 
  nsreachable n1 s1 -> nsreachable n2 s2 ->
  move s1 s2 -> n1 = n2 \/ n1 = S n2 \/ S n1 = n2.
Proof.
intros H1 H2 H3.
assert (F1: nreachable (S n2) s1).
  apply nreachS with s2; auto.
  + case H2; auto.
  + apply move_sym; auto.
    apply nreachable_valid with n1; case H1; auto.
  + case (nsreachable_bound _ _ F1); intros k (Hk, Hk1).
    assert (k = n1); subst.
      apply nsreachable_unique with s1; auto.
    assert (F2: nreachable (S n1) s2).
      apply nreachS with s1; auto.
      case H1; auto.
    case (nsreachable_bound _ _ F2); intros k1 (Hk2, Hk3).
    assert (k1 = n2); subst.
      apply nsreachable_unique with s2; auto.
    case (le_lt_or_eq _ _ Hk); clear Hk; intros Hk; subst; auto.
    case (le_lt_or_eq _ _ Hk2); clear Hk2; intros Hk2; subst; auto.
    left; apply le_antisym; auto with arith.
Qed.

Lemma porder_move_down s1 s2 n1 n2 : 
  nsreachable n1 s1 -> nsreachable n2 s2 ->
  move s1 s2 -> porder n2 = pos_down (porder n1) -> n1 = S n2.
Proof.
intros H1 H2 H3; generalize (porder_move _ _ _ _ H1 H2 H3);
  intros [HH | [HH | HH]]; auto.
- intros HH1; contradict HH1; 
  generalize (porder_inv n1); intros [HH2 | [HH2 | HH2]]; subst; rewrite HH2;
  intros HH3; discriminate.
- intros HH1; contradict HH1; subst; rewrite porderS; 
  generalize (porder_inv n1); intros [HH2 | [HH2 | HH2]];
  rewrite HH2;
  intros HH3; discriminate.
Qed.

Lemma get_next_correct n n1 s s1 s2 :
  (s1, s2) = fst (iter2s n) -> n1 < n ->
  nsreachable (S n1) s -> 
  match get_next s s1 s2 with Some m => nsreachable n1 (m2f m s)
  | None => False end.
Proof.
generalize (iter2s_correct n) 
  (fun n1 s => get_number_correct n n1 s s1 s2); case iter2s.
intros (s3, s4) ss; simpl; intros (H1, (H2, H3)) Hn HH Hl Hr.
injection HH; intros; subst s3 s4; clear HH.
case (move_nsreachable _ _ Hr); intros s3 (Hs1, Hs2).
case (fun x => (move_Movel _ _ (move_sym _ _ x Hs1))).
case Hs2; intros H4 _; apply nreachable_valid with (1 := H4).
intros a (Ha, Ha1); subst.
unfold get_next.
generalize (get_next_aux_correct (pos_down (get_number s s1 s2)) s s1 s2 Movel);
  case get_next_aux.
- intros a1 (Ha2, Ha3).
  rewrite <- (Hn (S n1) s) in Ha3; auto with arith.
  assert (F1: nreachable (S (S n1)) (m2f a1 s)).
    apply nreachS with s; auto.
    + case Hr; auto.
    + apply Movel_move; auto.
    + case (nsreachable_bound _ _ F1); intros k1 (Hk2, Hk3).
      assert (F2: nreachable (S k1) s).
        apply nreachS with (m2f a1 s); auto.
        * case Hk3; auto.
        * apply move_sym; try apply Movel_move; auto.
          apply nreachable_valid with (S n1); case Hr; auto.
        * case (nsreachable_bound _ _ F2); intros k2 (Hk4, Hk5).
          assert (k2 = (S n1)); subst.
            apply nsreachable_unique with (2 := Hr); auto.
          case (le_lt_or_eq n1 k1); auto with arith; clear Hk4; 
            intros Hk4; subst; auto.
          case (le_lt_or_eq _ _ Hk2); clear Hk2; intros Hk2.
          -- rewrite <- (Hn k1) in Ha3; auto with arith.
             ++ rewrite porderS, pos_down_up in Ha3; auto.
                ** case (le_lt_or_eq k1 (S n1)); auto with arith.
                   --- intros HH; contradict HH; auto with arith.
                   --- intros HH; subst; contradict Ha3.
                       rewrite porderS.
                       case (porder n1); simpl; auto;
                         try (intros; discriminate).
                       intros p; case p; intros; discriminate.
                ** generalize (porder_inv n1); intros [HH1|[HH1|HH1]]; 
                     rewrite HH1; red; auto.
             ++ apply le_trans with (S n1); auto with arith.
          -- subst k1; clear F1 F2.
             case (le_or_lt (S (S n1)) n); intros Hk6.
             ++ rewrite <- (Hn (S (S n1))) in Ha3; auto with arith.
                contradict Ha3; repeat rewrite porderS.
                case (porder n1); simpl; auto; try (intros; discriminate).
                intros p; case p; intros; discriminate.
             ++ assert (F1: get_number (m2f a1 s) s1 s2 = 4%positive).
                ** unfold get_number.
                   generalize (in_states_correct (m2f a1 s) s1); 
                     case in_states; intros G1.
                   --- rewrite H1 in G1.
                       contradict Hk6; case G1; intros k (Hk, (Hk1,Hk2)).
                       assert (k = S (S n1)); subst; auto with arith.
                       apply nsreachable_unique with (1 := Hk1); auto.
                   --- generalize (in_states_correct (m2f a1 s) s2); 
                         case in_states; intros G2; auto.
                       rewrite H2 in G2.
                       contradict Hk6; case G2; intros k (Hk, (Hk1,Hk2)).
                       assert (k = S (S n1)); subst; auto with arith.
                       apply nsreachable_unique with (1 := Hk1); auto.
                ** contradict Ha3; rewrite F1.
                   case porder; simpl; try (intros; discriminate);
                   intros p; case p; intros; discriminate.
- intros HH; case (HH a); auto.
  rewrite <- (Hn n1 (m2f a s)); auto with arith.
  rewrite <- (Hn (S n1)); auto with arith.
  rewrite porderS, pos_down_up; auto;
  generalize (porder_inv n1); intros [HH1|[HH1|HH1]]; rewrite HH1; red; auto.
Qed.

Lemma get_next_init n s1 s2 :  
  (s1, s2) = fst (iter2s n) -> get_next init_state s1 s2  = None.
Proof.
generalize (iter2s_correct n) 
  (fun n1 s => get_number_correct n n1 s s1 s2); case iter2s.
intros (s3, s4) ss; simpl; intros (H1, (H2, H3)) Hn HH.
injection HH; intros; subst s3 s4; clear HH.
unfold get_next.
replace (get_number init_state s1 s2) with 1%positive.
- simpl pos_down.
  generalize (get_next_aux_correct 3 init_state s1 s2 Movel);
    case get_next_aux; auto.
  intros a (Ha, Ha1).
  generalize Ha1; unfold get_number.
  generalize (in_states_correct (m2f a init_state) s1); case in_states;
    intros G1.
  rewrite H1 in G1.
  case G1; intros k (Hk, (Hk1,Hk2)).
  generalize (in_states_correct (m2f a init_state) s2); case in_states; 
    intros G2; auto.
  + rewrite H2 in G2.
    case G2; intros k1 (Hk3, (Hk4,Hk5)).
    case (porder_move init_state (m2f a init_state) 0 k); auto.
    * split; try apply nreach0; intros m Hm; contradict Hm; auto with arith.
    * apply Movel_move; auto.
    * intros HH; subst k.
      case (porder_move init_state (m2f a init_state) 0 k1); auto.
      -- split; try apply nreach0; intros m Hm; contradict Hm; auto with arith.
      -- apply Movel_move; auto.
      -- intros HH; subst k1.
         case Hk5; simpl; auto.
      -- intros HH; case HH; clear HH; intros HH; try discriminate; subst k1.
         absurd (0 = 1); auto with arith.
         apply nsreachable_unique with (1 := Hk1); auto.
    * intros HH; case HH; clear HH; intros HH; try discriminate; subst k.
      case Hk2; simpl; auto.
  + intros; discriminate.
  + case in_states; intros; discriminate.
- unfold get_number.
  generalize (in_states_correct init_state s1); case in_states; intros G1.
  + generalize (in_states_correct init_state s2); case in_states;
      intros G2; auto.
    rewrite H2 in G2.
    case G2; intros k (Hk, (Hk1,Hk2)).
    assert (k = 0); subst.
      apply nsreachable_unique with init_state; auto.
      split; try apply nreach0; intros m Hm; contradict Hm; auto with arith.
    case Hk2; auto.
   + case G1; rewrite H1; exists 0; repeat (split; auto with arith);
       try constructor.
     intros m Hm; contradict Hm; auto with arith.
Qed.

Lemma solve_correct n m p s s1 s2 :
  (s1, s2) = fst (iter2s n) -> m <= n ->
  nsreachable m s -> 
  nsreachable (m - p) (fold_left (fun s a => m2f a s) (solve p s s1 s2) s).
Proof.
intro H; generalize m s; elim p; clear m p s; simpl; auto.
intros m; rewrite <- minus_n_O; auto.
intros p Hrec m; case m; clear m; simpl.
- intros s _ HH; case HH; intros HH1 _; inversion_clear HH1.
  rewrite get_next_init with (1 := H).
  split; try apply nreach0; intros m1 Hm1; contradict Hm1; auto with arith.
- intros m s H1 H2.
  assert (F1: m < n); auto with arith.
  generalize (get_next_correct _ _ _ _ _  H F1 H2); case get_next.
  + intros a Ha; rewrite fold_left_cons.
    apply Hrec; auto with arith.
  +intros HH; case HH.
Qed.

(* Main theorem: we get a path to the initial state *)

Lemma solve_init n s s1 s2 :
  (s1, s2) = fst (iter2s n) ->
  nlreachable n s -> 
  fold_left (fun s a => m2f a s) (solve n s s1 s2) s = init_state.
Proof.
intros H1 H2.
case (nlreachable_bound _ _ H2); clear H2; intros m (H2, H3).
generalize (solve_correct n m n s s1 s2 H1 H2 H3).
replace (m - n) with 0.
- intros (HH,_); inversion HH; auto.
- case (le_lt_or_eq _ _ H2); intros HH; subst; auto with arith.
  rewrite not_le_minus_0; auto with arith.
Qed.

(* Main theorem: and the path is "small"*)

Lemma solve_length n s s1 s2 :
  length (solve n s s1 s2) <= n.
Proof.
revert s s1 s2; elim n; simpl; auto; clear n.
intros n Hrec s s1 s2; case get_next; simpl; auto with arith.
Qed.
