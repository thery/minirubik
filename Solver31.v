Require Import Int31 List BasicRubik Rubik31.

CoInductive val12 := Mval12: tc2 * tc2 -> val12.

Definition make_val12 := Mval12 (iter 12).

Definition s11 := match make_val12 with Mval12 x => fst x end.
Definition l11 := match make_val12 with Mval12 x => snd x end.

Lemma s11_l11: (s11,l11) = iter 12.
Proof.
unfold s11, l11, make_val12; case (iter 12);
 intros; apply refl_equal.
Qed.

Lemma l11_ok: l11 = OTC2.
Proof.
native_cast_no_check (refl_equal OTC2).
Time Qed.

Lemma s11_correct: (s11, OTC2) = iter 12.
Proof.
apply trans_equal with (s11,l11).
  apply f_equal2 with (f := @pair _ _).
    now apply refl_equal.
  apply sym_equal.
  now exact l11_ok. 
exact s11_l11.
Time Qed.

Lemma reach11 s : reachable s -> nlreachable 11 s.
Proof.
revert s.
assert (F1: forall n ss, (ss, OTC2) = iter (S n) ->
              forall s, reachable s -> nlreachable n s).
  intros n ss Hss s Hs; generalize Hss (iter_final (S n));
    case iter.
  intros s1 s2; case s2; auto.
  now intros t1 t2 HH; discriminate HH.
intros; apply F1 with s11.
  now exact s11_correct.
exact H.
Qed.

Lemma s11_all : tc2all s11 = true.
Proof.
native_cast_no_check (refl_equal true).
Time Qed.

Lemma valid11 s : valid_state s -> reachable s.
Proof.
revert s.
assert (F1: forall n ss, (ss, OTC2) = iter n -> 
              tc2all ss = true ->
              forall s, valid_state s -> reachable s).
  intros n ss Hss Hc s Hs.
  apply nlreachable_reachable with n; auto.
  apply (iter_true_reachable n s Hs).
  rewrite <- Hss; simpl fst.
  generalize (encode_valid _ Hs); case (encode_state s).
  intros (l1,l2) p (Hp1, (Hp2, Hp3)).
  now apply checktc2_all; auto.
intros s Hs.
exact (F1 12%nat s11 s11_correct s11_all s Hs).
Qed.

Lemma validreach11 s : valid_state s -> nlreachable 11 s.
intros; apply reach11; apply valid11; auto.
Qed.

CoInductive val11 := Mval11: tc2 * tc2 * tc2 -> val11.

Definition make_val11 := Mval11 (iter2 11).

Definition ss := match make_val11 with Mval11 x => fst x end.

Definition s1 := fst ss.
Definition s2 := snd ss.

Lemma s12: (s1,s2) = fst (iter2 11).
Proof.
unfold s1, s2, ss, make_val11; case (iter2 11); simpl; auto.
intros p; case p; auto.
Qed.

Definition solve s := tc2_solve 11 s s1 s2.

Theorem solve_eq : forall s, solve s = tc2_solve 11 s s1 s2.
Proof.
intros s; unfold solve; apply refl_equal.
Qed.

Lemma solve_init s :
  valid_state s -> 
  fold_left (fun s a => m2f a s) (solve s) s = init_state.
Proof.
intros Hs.
apply trans_equal with
 (fold_left (fun s a => m2f a s) (tc2_solve 11 s s1 s2) s).
  apply f_equal3 with (f := @fold_left _ _).
    now apply refl_equal.
    now exact (solve_eq s).
  now apply refl_equal.
apply tc2_solve_init.
  now exact s12.
apply validreach11; auto.
Qed.

Lemma solve_length s :
  valid_state s -> length (solve s) <= 11.
Proof.
intro Hs.
assert (tmp: forall a b c, a = b -> a <= c -> b <= c).
  now intros a b c H1 H2; rewrite <- H1; auto.
apply tmp with (length (tc2_solve 11 s s1 s2)).
  apply f_equal with (f := @length _).
  now apply sym_equal; exact (solve_eq s).
apply tc2_solve_length.
  now exact s12.
exact Hs.
Qed.
