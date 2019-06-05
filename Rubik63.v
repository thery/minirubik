Require Import Int63 Cyclic63 List BasicRubik.

(** Cubes positions. There are 7*6*5*4*3*2 positions.                        **)
(** We code them as 7 * 4 * 3 * (2 * 6 * 5 = 30)                             **) 

Inductive tc7 := OTC7 | TC7 (_ _ _ _ _ _ _: int).
Inductive tc4 := OTC4 | TC4 (_ _ _ _: tc7).
Inductive tc3 := OTC3 | TC3 (_ _ _: tc4).

(** Orientations: there is 3 possible orientations                          **)
(** about of 8 cubes, one is fixed and one has the orientations             **)
(** that depend of the others so 3^6                                        **)

Inductive to1 := OTO1 | TO1 (_ _ _: tc3).
Inductive to2 := OTO2 | TO2 (_ _ _: to1).
Inductive to3 := OTO3 | TO3 (_ _ _: to2).
Inductive to4 := OTO4 | TO4 (_ _ _: to3).
Inductive to5 := OTO5 | TO5 (_ _ _: to4).
Inductive to6 := OTO6 | TO6 (_ _ _: to5).


(** Some 63 bits operations                                                  **)

Open Scope int63_scope.

Definition p2t63 x := snd (positive_to_int x) - 1.

Definition shiftr63 x n := addmuldiv (63 - n) 0 x.
Definition shiftl63 x n := addmuldiv n x 0.

Eval  native_compute in shiftr63 24 2.

(** Check if a given position is in a state                                  **)

Definition int63i x n := 
  let u := p2t63 n in
  let v := shiftr63 x u in
  let w := shiftl63 (shiftr63 v 1) 1 in
  match compare v w with Eq => false | _ => true end.

Definition tc7i l c n:= 
  match c, l  with 
  | TC7 m _ _ _ _ _ _, C1 :: _ => int63i m n
  | TC7 _ m _ _ _ _ _, C2 :: _ => int63i m n
  | TC7 _ _ m _ _ _ _, C3 :: _ => int63i m n
  | TC7 _ _ _ m _ _ _, C4 :: _ => int63i m n
  | TC7 _ _ _ _ m _ _, C5 :: _ => int63i m n
  | TC7 _ _ _ _ _ m _, C6 :: _ => int63i m n
  | TC7 _ _ _ _ _ _ m, C7 :: _ => int63i m n
  | _, _ => false
  end.

Definition tc4i l c n:= 
  match c, l  with 
  | TC4 m _ _ _, C1 :: l1 => tc7i l1 m n
  | TC4 _ m _ _, C2 :: l1 => tc7i l1 m n
  | TC4 _ _ m _, C3 :: l1 => tc7i l1 m n
  | TC4 _ _ _ m, C4 :: l1 => tc7i l1 m n
  | _, _ => false
  end.

Definition tc3i l c n := 
  match c, l  with 
  | TC3 m _ _, C1 :: l1 => tc4i l1 m n
  | TC3 _ m _, C2 :: l1 => tc4i l1 m n
  | TC3 _ _ m, C3 :: l1 => tc4i l1 m n
  | _, _ => false
  end.


Definition to1i l c l1 n := 
  match c, l  with 
  | TO1 m _ _, O1 :: _ => tc3i l1 m n
  | TO1 _ m _, O2 :: _ => tc3i l1 m n
  | TO1 _ _ m, O3 :: _ => tc3i l1 m n
  | _, _ => false
  end.


Definition to2i l c l1 n := 
  match c, l  with 
  | TO2 m _ _, O1 :: l2 => to1i l2 m l1 n
  | TO2 _ m _, O2 :: l2 => to1i l2 m l1 n
  | TO2 _ _ m, O3 :: l2 => to1i l2 m l1 n
  | _, _ => false
  end.

Definition to3i l c l1 n:= 
  match c, l  with 
  | TO3 m _ _, O1 :: l2 => to2i l2 m l1 n
  | TO3 _ m _, O2 :: l2 => to2i l2 m l1 n
  | TO3 _ _ m, O3 :: l2 => to2i l2 m l1 n
  | _, _ => false
  end.

Definition to4i l c l1 n:= 
  match c, l  with 
  | TO4 m _ _, O1 :: l2 => to3i l2 m l1 n
  | TO4 _ m _, O2 :: l2 => to3i l2 m l1 n
  | TO4 _ _ m, O3 :: l2 => to3i l2 m l1 n
  | _, _ => false
  end.

Definition to5i l c l1 n := 
  match c, l  with 
  | TO5 m _ _, O1 :: l2 => to4i l2 m l1 n
  | TO5 _ m _, O2 :: l2 => to4i l2 m l1 n
  | TO5 _ _ m, O3 :: l2 => to4i l2 m l1 n
  | _, _ => false
  end.

Definition to6i l c l1 n := 
  match c, l  with 
  | TO6 m _ _, O1 :: l2 => to5i l2 m l1 n
  | TO6 _ m _, O2 :: l2 => to5i l2 m l1 n
  | TO6 _ _ m, O3 :: l2 => to5i l2 m l1 n
  | _, _ => false
  end.

(** Add a position in a state                                                **)

Definition int63a x n := 
  add x (shiftl63 1 (p2t63 n)).

Definition tc7a l c n := 
  match l, c  with 
  | C1 :: _, TC7 m m0 m1 m2 m3 m4 m5 => TC7 (int63a m n) m0 m1 m2 m3 m4 m5
  | C2 :: _, TC7 m0 m m1 m2 m3 m4 m5 => TC7 m0 (int63a m n) m1 m2 m3 m4 m5
  | C3 :: _, TC7 m0 m1 m m2 m3 m4 m5 => TC7 m0 m1 (int63a m n) m2 m3 m4 m5
  | C4 :: _, TC7 m0 m1 m2 m m3 m4 m5 => TC7 m0 m1 m2 (int63a m n) m3 m4 m5
  | C5 :: _, TC7 m0 m1 m2 m3 m m4 m5 => TC7 m0 m1 m2 m3 (int63a m n) m4 m5
  | C6 :: _, TC7 m0 m1 m2 m3 m4 m m5 => TC7 m0 m1 m2 m3 m4 (int63a m n) m5
  | C7 :: _, TC7 m0 m1 m2 m3 m4 m5 m => TC7 m0 m1 m2 m3 m4 m5 (int63a m n)
  | C1 :: _, OTC7 => TC7 (int63a 0 n) 0 0 0 0 0 0
  | C2 :: _, OTC7 => TC7 0 (int63a 0 n) 0 0 0 0 0
  | C3 :: _, OTC7 => TC7 0 0 (int63a 0 n) 0 0 0 0
  | C4 :: _, OTC7 => TC7 0 0 0 (int63a 0 n) 0 0 0 
  | C5 :: _, OTC7 => TC7 0 0 0 0 (int63a 0 n) 0 0
  | C6 :: _, OTC7 => TC7 0 0 0 0 0 (int63a 0 n) 0
  | C7 :: _, OTC7 => TC7 0 0 0 0 0 0 (int63a 0 n)
  | _, _ => c
  end.

Definition tc4a l c n := 
  match l, c  with 
  | C1 :: l1, TC4 m m0 m1 m2 => TC4 (tc7a l1 m n) m0 m1 m2
  | C2 :: l1, TC4 m0 m m1 m2 => TC4 m0 (tc7a l1 m n) m1 m2
  | C3 :: l1, TC4 m0 m1 m m2 => TC4 m0 m1 (tc7a l1 m n) m2
  | C4 :: l1, TC4 m0 m1 m2 m => TC4 m0 m1 m2 (tc7a l1 m n)
  | C1 :: l1, OTC4 => TC4 (tc7a l1 OTC7 n) OTC7 OTC7 OTC7
  | C2 :: l1, OTC4 => TC4 OTC7 (tc7a l1 OTC7 n) OTC7 OTC7
  | C3 :: l1, OTC4 => TC4 OTC7 OTC7 (tc7a l1 OTC7 n) OTC7
  | C4 :: l1, OTC4 => TC4 OTC7 OTC7 OTC7 (tc7a l1 OTC7 n)
  | _, _ => c
  end.

Definition tc3a l c n := 
  match l, c  with 
  | C1 :: l1, TC3 m m0 m1 => TC3 (tc4a l1 m n) m0 m1
  | C2 :: l1, TC3 m0 m m1 => TC3 m0 (tc4a l1 m n) m1
  | C3 :: l1, TC3 m0 m1 m => TC3 m0 m1 (tc4a l1 m n)
  | C1 :: l1, OTC3 => TC3 (tc4a l1 OTC4 n) OTC4 OTC4
  | C2 :: l1, OTC3 => TC3 OTC4 (tc4a l1 OTC4 n) OTC4
  | C3 :: l1, OTC3 => TC3 OTC4 OTC4 (tc4a l1 OTC4 n)
  | C_, _ => c
  end.

Definition to1a l c l1 n:= 
  match l, c  with 
  | O1 :: _, TO1 m m0 m1 => TO1 (tc3a l1 m n) m0 m1
  | O2 :: _, TO1 m0 m m1 => TO1 m0 (tc3a l1 m n) m1
  | O3 :: _, TO1 m0 m1 m => TO1 m0 m1 (tc3a l1 m n)
  | O1 :: _, OTO1 => TO1 (tc3a l1 OTC3 n) OTC3 OTC3
  | O2 :: _, OTO1 => TO1 OTC3 (tc3a l1 OTC3 n) OTC3
  | O3 :: _, OTO1 => TO1 OTC3 OTC3 (tc3a l1 OTC3 n)
  | _, _ => c
  end.

Definition to2a l c l1 n := 
  match l, c  with 
  | O1 :: l2, TO2 m m0 m1 => TO2 (to1a l2 m l1 n) m0 m1
  | O2 :: l2, TO2 m0 m m1 => TO2 m0 (to1a l2 m l1 n) m1
  | O3 :: l2, TO2 m0 m1 m => TO2 m0 m1 (to1a l2 m l1 n)
  | O1 :: l2, OTO2 => TO2 (to1a l2 OTO1 l1 n) OTO1 OTO1
  | O2 :: l2, OTO2 => TO2 OTO1 (to1a l2 OTO1 l1 n) OTO1
  | O3 :: l2, OTO2 => TO2 OTO1 OTO1 (to1a l2 OTO1 l1 n)
  | _, _ => c
  end.

Definition to3a l c l1 n := 
  match l, c  with 
  | O1 :: l2, TO3 m m0 m1 => TO3 (to2a l2 m l1 n) m0 m1
  | O2 :: l2, TO3 m0 m m1 => TO3 m0 (to2a l2 m l1 n) m1
  | O3 :: l2, TO3 m0 m1 m => TO3 m0 m1 (to2a l2 m l1 n)
  | O1 :: l2, OTO3 => TO3 (to2a l2 OTO2 l1 n) OTO2 OTO2
  | O2 :: l2, OTO3 => TO3 OTO2 (to2a l2 OTO2 l1 n) OTO2
  | O3 :: l2, OTO3 => TO3 OTO2 OTO2 (to2a l2 OTO2 l1 n)
  | _, _ => c
  end.

Definition to4a l c l1 n := 
  match l, c  with 
  | O1 :: l2, TO4 m m0 m1 => TO4 (to3a l2 m l1 n) m0 m1
  | O2 :: l2, TO4 m0 m m1 => TO4 m0 (to3a l2 m l1 n) m1
  | O3 :: l2, TO4 m0 m1 m => TO4 m0 m1 (to3a l2 m l1 n)
  | O1 :: l2, OTO4 => TO4 (to3a l2 OTO3 l1 n) OTO3 OTO3
  | O2 :: l2, OTO4 => TO4 OTO3 (to3a l2 OTO3 l1 n) OTO3
  | O3 :: l2, OTO4 => TO4 OTO3 OTO3 (to3a l2 OTO3 l1 n)
  | _, _ => c
  end.

Definition to5a l c l1 n := 
  match l, c  with 
  | O1 :: l2, TO5 m m0 m1 => TO5 (to4a l2 m l1 n) m0 m1
  | O2 :: l2, TO5 m0 m m1 => TO5 m0 (to4a l2 m l1 n) m1
  | O3 :: l2, TO5 m0 m1 m => TO5 m0 m1 (to4a l2 m l1 n)
  | O1 :: l2, OTO5 => TO5 (to4a l2 OTO4 l1 n) OTO4 OTO4
  | O2 :: l2, OTO5 => TO5 OTO4 (to4a l2 OTO4 l1 n) OTO4
  | O3 :: l2, OTO5 => TO5 OTO4 OTO4 (to4a l2 OTO4 l1 n)
  | _, _ => c
  end.

Definition to6a l c l1 n := 
  match l, c  with 
  | O1 :: l2, TO6 m m0 m1 => TO6 (to5a l2 m l1 n) m0 m1
  | O2 :: l2, TO6 m0 m m1 => TO6 m0 (to5a l2 m l1 n) m1
  | O3 :: l2, TO6 m0 m1 m => TO6 m0 m1 (to5a l2 m l1 n)
  | O1 :: l2, OTO6 => TO6 (to5a l2 OTO5 l1 n) OTO5 OTO5
  | O2 :: l2, OTO6 => TO6 OTO5 (to5a l2 OTO5 l1 n) OTO5
  | O3 :: l2, OTO6 => TO6 OTO5 OTO5 (to5a l2 OTO5 l1 n)
  | _, _ => c
  end.

(** Iteration                                                                **)

Section Iter.

Variable A : Type.
Variable next: A -> list cube -> list orientation -> positive -> A.

Fixpoint int63it_aux (m : nat) (p : positive) 
                     (c1 to6 : int) (lc : list cube) (lo : list orientation)
                     (a : A) {struct m} :=
 match m with 
 | O => a 
 | S m1 => 
    let a1 := match compare c1 (shiftl63 to6 1) with 
              | Eq => a 
              | _  => next a lc lo p 
              end in
    int63it_aux m1 (Pos.succ p) to6 (shiftr63 to6 1) lc lo a1
 end.

Definition int63it a lc lo c := int63it_aux 60 1%positive c (shiftr63 c 1) a lc lo.

Definition tc7it lc lo a c := 
  match c  with 
  | TC7 m0 m1 m2 m3 m4 m5 m6 => 
   int63it (C1 :: lc) lo 
     (int63it (C2 :: lc) lo  
       (int63it (C3 :: lc) lo 
         (int63it (C4 :: lc) lo
           (int63it (C5 :: lc) lo
             (int63it (C6 :: lc) lo
               (int63it (C7 :: lc) lo a m6) m5) m4) m3) m2) m1) m0
  | _ => a
  end.

Definition tc4it lc lo a c := 
  match c  with 
  | TC4 m0 m1 m2 m3 => tc7it (C1 :: lc) lo 
                      (tc7it (C2 :: lc) lo 
                        (tc7it (C3 :: lc) lo 
                          (tc7it (C4 :: lc) lo a m3) m2) m1) m0
  | _ => a
  end.

Definition tc3it lc lo a c := 
  match c  with 
  | TC3 m0 m1 m2 => tc4it (C1 :: lc) lo 
                    (tc4it (C2 :: lc) lo  
                      (tc4it (C3 :: lc) lo a m2) m1) m0
  | _ => a
  end.

Definition to1it lc lo a c := 
  match c  with 
  | TO1 m0 m1 m2 => tc3it lc (O1 :: lo) 
                    (tc3it lc (O2 :: lo)  
                      (tc3it lc (O3 :: lo) a m2) m1) m0
  | _ => a
  end.

Definition to2it lc lo a c := 
  match c  with 
  | TO2 m0 m1 m2 => to1it lc (O1 :: lo) 
                    (to1it lc (O2 :: lo)  
                      (to1it lc (O3 :: lo) a m2) m1) m0
  | _ => a
  end.

Definition to3it lc lo a c := 
  match c  with 
  | TO3 m0 m1 m2 => to2it lc (O1 :: lo) 
                    (to2it lc (O2 :: lo)  
                      (to2it lc (O3 :: lo) a m2) m1) m0
  | _ => a
  end.

Definition to4it lc lo a c := 
  match c  with 
  | TO4 m0 m1 m2 => to3it lc (O1 :: lo) 
                    (to3it lc (O2 :: lo)  
                      (to3it lc (O3 :: lo) a m2) m1) m0
  | _ => a
  end.

Definition to5it lc lo a c := 
  match c  with 
  | TO5 m0 m1 m2 => to4it lc (O1 :: lo) 
                    (to4it lc (O2 :: lo)  
                      (to4it lc (O3 :: lo) a m2) m1) m0
  | _ => a
  end.

Definition to6it a c := 
  match c  with 
  | TO6 m0 m1 m2 => to5it nil (O1 :: nil) 
                    (to5it nil (O2 :: nil)  
                      (to5it nil (O3 :: nil) a m2) m1) m0
  | _ => a
  end.

End Iter.

Eval  native_compute in int63it _ (fun x l1 l2 y => y :: x) nil nil nil 2345.

 
(** Check that all states have been checked                                  **)

Definition int63all c:=
  match compare c 1152921504606846975 with Eq => true | _ => false end.

Definition tc7all c := 
  match c  with 
  | TC7 m0 m1 m2 m3 m4 m5 m6 => 
   (int63all m0 && int63all m1 && int63all m2 && int63all m3 && 
    int63all m4 && int63all m5 && int63all m6)%bool
  | _ => false
  end.

Definition tc4all c := 
  match c  with 
  | TC4 m0 m1 m2 m3 => 
   (tc7all m0 && tc7all m1 && tc7all m2 && tc7all m3)%bool
  | _ => false
  end.

Definition tc3all c := 
  match c  with 
  | TC3 m0 m1 m2 => 
   (tc4all m0 && tc4all m1 && tc4all m2)%bool
  | _ => false
  end.

Definition to1all c := 
  match c  with 
  | TO1 m0 m1 m2 => 
   (tc3all m0 && tc3all m1 && tc3all m2)%bool
  | _ => false
  end.

Definition to2all c := 
  match c  with 
  | TO2 m0 m1 m2 => 
   (to1all m0 && to1all m1 && to1all m2)%bool
  | _ => false
  end.

Definition to3all c := 
  match c  with 
  | TO3 m0 m1 m2 => 
   (to2all m0 && to2all m1 && to2all m2)%bool
  | _ => false
  end.

Definition to4all c := 
  match c  with 
  | TO4 m0 m1 m2 => 
   (to3all m0 && to3all m1 && to3all m2)%bool
  | _ => false
  end.


Definition to5all c := 
  match c  with 
  | TO5 m0 m1 m2 => 
   (to4all m0 && to4all m1 && to4all m2)%bool
  | _ => false
  end.

Definition to6all c := 
  match c  with 
  | TO6 m0 m1 m2 => 
   (to5all m0 && to5all m1 && to5all m2)%bool
  | _ => false
  end.
 
(** encoding/decoding: a state as a number                                   **)
Fixpoint encode_aux l n :=
  match l with 
  | nil => nil
  | m :: l1 => (match cube_compare n m with Lt => cube_pred m | _ => m end) :: 
             encode_aux l1 n
  end. 

Fixpoint encode l n:= 
  match l, n with 
  | m :: l1, (S n1) => m ::  encode (encode_aux l1 m) n1
  | _, _ => nil
  end.

Fixpoint decode_aux l n :=
  match l with 
  | nil => nil
  | m :: l1 => (match cube_compare n m with Gt => m | _ => cube_succ m end) :: 
             decode_aux l1 n
  end. 

Fixpoint decode l := 
  match l with 
  | m :: l1  => m ::  decode_aux (decode l1) m
  | _ => nil
  end.

(*
Eval  native_compute in decode (encode (C1 :: C2 :: C3 :: nil) 3). 

Eval  native_compute in decode (encode (C1 :: C3 :: C2 :: nil) 3). 

Eval  native_compute in decode (encode (C2 :: C1 :: C3 :: nil) 3).
 
Eval  native_compute in decode (encode (C2 :: C3 :: C1 :: nil) 3).

Eval  native_compute in decode (encode (C3 :: C1 :: C2 :: nil) 3).

Eval  native_compute in decode (encode (C3 :: C2 :: C1 :: nil) 3).
*)

Section Memo.

Variable A: Set.
Variable f: list cube -> A.

CoInductive memo_val: Type := mval:  A -> memo_val.

CoFixpoint val_make (l : list cube) := mval (f (rev l)).

CoInductive MStream: Set :=
 MSeq (a : memo_val) (m1 m2 m3 m4 m5 m6 m7: MStream).

CoFixpoint memo_make (l : list cube): MStream:= 
   MSeq (val_make l)  (memo_make (C1 :: l))
       (memo_make (C2 :: l)) (memo_make (C3 :: l)) (memo_make (C4 :: l)) 
       (memo_make (C5 :: l)) (memo_make (C6 :: l)) (memo_make (C7 :: l)).

Fixpoint memo_get_val (l : list cube) (m : MStream) {struct l} : A :=
match l with 
   nil =>   match m with MSeq (mval a) _ _ _ _ _ _ _  => a end
| C1 :: l1 => match m with MSeq _ m1 _ _ _ _ _ _ => 
              memo_get_val l1 m1
            end
| C2 :: l1 => match m with MSeq _ _ m1 _ _ _ _ _ => 
              memo_get_val l1 m1
            end
| C3 :: l1 => match m with MSeq _ _ _ m1 _ _ _ _ => 
              memo_get_val l1 m1
            end
| C4 :: l1 => match m with MSeq _ _ _ _ m1 _ _ _  => 
              memo_get_val l1 m1
            end
| C5 :: l1 => match m with MSeq _ _ _ _ _ m1 _ _ => 
              memo_get_val l1 m1
            end
| C6 :: l1 => match m with MSeq _ _ _ _ _ _ m1 _ => 
              memo_get_val l1 m1
            end
| C7 :: l1 => match m with MSeq _ _ _ _ _ _ _ m1 => 
              memo_get_val l1 m1
            end
end.

Lemma memo_get_val_correct l1 : memo_get_val l1 (memo_make nil) = f l1.
Proof.
revert l1.
assert (H : forall l1 l2, memo_get_val l1 (memo_make l2) = f (rev l2 ++ l1)).
  induction l1 as [ | a l1 Hrec].
    intros l2; rewrite <- app_nil_end; auto.
  intros l2; case a; clear a; simpl; rewrite Hrec; simpl; rewrite app_ass; auto.
intros l1; rewrite H; auto.
Qed.

End Memo.

Definition encode_memo_list :=  memo_make _ (fun x => encode x 6) nil.

Definition encode_memo l := memo_get_val _ l encode_memo_list.

Definition encode_state s := 
  match s with
  | State i7 i6 i5 i4 i3 i2 i1 o1 o2 o3 o4 o5 o6 o7 =>
    match encode_memo (i7 :: i6 :: i5 :: i4 :: i3 :: i2 :: nil) with
    | p7 :: p6 :: p5 :: p4 :: p3 :: p2 :: l => 
      (p3 :: p4 :: p7 :: nil,
       o6 :: o5 :: o4 :: o3 :: o2 :: o1 :: nil, cube3_encode p2 p5 p6)
    |  _ => (nil, nil, 1%positive)
    end
  end.

Definition decode_memo_list :=  memo_make _ decode nil.

Definition decode_memo l := memo_get_val _ l decode_memo_list.

Definition decode_state lc lo n := 
  match lc, lo with
  | p7 :: p4 :: p3 :: nil, o1 :: o2 :: o3 :: o4 :: o5 :: o6 :: nil => 
       let (pp, p6) := cube3_decode n in 
       let (p2, p5) := pp in
       let o7 := oinv (oadd o1 (oadd o2 (oadd o3 (oadd o4 (oadd o5 o6))))) in
       match decode_memo (p7 :: p6 :: p5 :: p4 :: p3 :: p2 :: C1 :: nil) with
         i7 :: i6 :: i5 :: i4 :: i3 :: i2 :: i1 :: nil =>
            State i7 i6 i5 i4 i3 i2 i1 o1 o2 o3 o4 o5 o6 o7 
       | _ => init_state
       end
  |  _, _ => init_state
  end.

Definition next (s : to6 * to6) lc lo n :=
 let s1 := decode_state lc lo n in
 fold_left 
  (fun (s : to6 * to6) f => 
    let (states, nstates) := s in
    let (u, n) := encode_state (f s1) in
    let (lc , lo) := u in
    if to6i lo states lc n then s else
    let states1 := to6a lo states lc n in
    let nstates1 := to6a lo nstates lc n in (states1, nstates1))
  movel s.

Definition addn s n :=  
 let (u, n) := encode_state n in
 let (lc , lo) := u in
 if to6i  lo s lc n then s else to6a lo s lc n.

Definition count (n : Z) (l : list cube) 
              (l1 : list orientation) (p: positive):= Z.succ n.

Definition countn s := to6it _ count 0%Z s.

Fixpoint iter_aux n (s : to6 * to6) := 
  match n with 
   O => s 
 | S n1 => let (m,p) := s in 
           iter_aux n1 
               (to6it _ next (m,OTO6) p)
  end.

Definition s0 := addn OTO6 init_state.

Definition iter n := iter_aux n (s0, s0).

Definition countns n := let x := iter n in (countn (fst x), countn (snd x)).

(*
Time Eval  native_compute in countns 0.
Time Eval  native_compute in countns 1.
Time Eval  native_compute in countns 2.
Time Eval  native_compute in countns 3.
Time Eval  native_compute in countns 4.
Time Eval  native_compute in countns 5.
Time Eval  native_compute in countns 6.
Time Eval  native_compute in countns 7.
Time Eval  native_compute in countns 8.
Time Eval  native_compute in countns 9.
Time Eval  native_compute in countns 10. 
Time Eval  native_compute in countns 11.
Time Eval  native_compute in countns 12.
*)

(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*                                                                           *)
(*                     PROOF PART                                            *)
(*                                                                           *)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)


(*****************************************************************************)
(*                                                                           *)
(*           Some properties of int                                        *)
(*                                                                           *)
(*****************************************************************************)

Lemma phi_addmuldiv63 (x y p : int):
     (to_Z p <= 63)%Z ->
     (to_Z (addmuldiv p x y) =
       ((to_Z x * 2 ^ to_Z p +  to_Z y / 2 ^ (63 - to_Z p)) mod 2^63))%Z.
Proof. apply addmuldiv_spec. Qed.

Definition phi0: to_Z 0 = 0%Z := (refl_equal 0%Z).
Definition phi1: to_Z 1 = 1%Z := (refl_equal 1%Z).
Definition phi63: to_Z 63 = 63%Z := (refl_equal 63%Z).

Definition phi_to_Z (x : int) : (0 <= to_Z x < 2 ^ 63)%Z := (to_Z_bounded x).

Lemma phi_nonneg (x : int) : (0 <= to_Z x)%Z.
Proof. now destruct (phi_to_Z x). Qed.

Definition phi_add (x y : int) :  
     (to_Z (x + y) = ((to_Z x + to_Z y) mod 2 ^ 63))%Z := (add_spec x y).

Definition phi_sub (x y : int) : 
     (to_Z (x - y) = ((to_Z x - to_Z y) mod 2 ^ 63))%Z := (sub_spec x y).

Lemma phi_shiftr63 p n :
  (to_Z n <= 63)%Z -> to_Z (shiftr63 p n) = (to_Z p / 2 ^ (to_Z n))%Z.
Proof.
intro H; unfold shiftr63.
case (phi_to_Z n); intros Hn1 Hn2.
case (phi_to_Z p); intros Hp1 Hp2.
rewrite phi_addmuldiv63; auto with zarith.
2: rewrite phi_sub; rewrite Zmod_small; rewrite phi63; auto with zarith.
2: split; auto with zarith.
2: apply Z.le_lt_trans with 63%Z; auto with zarith; red; auto.
rewrite phi0; rewrite Zmult_0_l; rewrite Zplus_0_l.
rewrite phi_sub; rewrite phi63.
rewrite (Zmod_small (63 - to_Z n)%Z).
2: split; auto with zarith.
2: apply Z.le_lt_trans with 63%Z; auto with zarith; red; auto.
replace (63 - (63 - to_Z n))%Z with (to_Z n); auto with zarith.
apply Z.mod_small; split; auto with zarith.
apply Z.div_pos; auto with zarith.
case (Zle_lt_or_eq _ _ Hp1); intros HH.
2: rewrite <- HH; rewrite Zdiv_0_l; auto with zarith.
apply Z.le_lt_trans with (to_Z p/ 2 ^ 0)%Z; auto with zarith.
case (Zle_lt_or_eq _ _ Hn1); intros HH1.
2: rewrite <- HH1; auto with zarith.
apply Zdiv_le_compat_l; auto with zarith.
split; auto with zarith.
apply Zpow_facts.Zpower_lt_monotone; auto with zarith.
rewrite Zpow_facts.Zpower_0_r; rewrite Zdiv_1_r; auto.
Qed.

Lemma phi_shiftl63 p n :
  (to_Z n <= 63)%Z -> (to_Z p * 2 ^ (to_Z n) < 2 ^63)%Z -> 
  (to_Z (shiftl63 p n) = to_Z p * (2 ^ (to_Z n)))%Z.
Proof.
intros H H1; unfold shiftl63.
case (phi_to_Z n); intros Hn1 Hn2.
case (phi_to_Z p); intros Hp1 Hp2.
rewrite phi_addmuldiv63; auto with zarith.
rewrite phi0; rewrite Zdiv_0_l; rewrite Zplus_0_r.
rewrite Zmod_small; auto with zarith.
Qed.

Lemma phi_p2t63 p : 
  (Zpos p <= 63 -> to_Z (p2t63 p) = Zpos p - 1)%Z.
Proof.
intros Hp; unfold p2t63.
rewrite phi_sub; rewrite phi1.
assert (Z.pos p = to_Z (snd (positive_to_int p))).
  generalize Hp.
  rewrite (positive_to_int_spec p).
  case (fst (positive_to_int p)); auto.
  intros p1 H; contradict H.
  rewrite N2Z.inj_pos.
  apply Zlt_not_le.
  replace 63%Z with (1 * 63 + 0)%Z; auto with zarith.
  apply Z.add_lt_le_mono; auto with zarith.
  2 : apply phi_nonneg.
  apply Zmult_lt_compat2; auto with zarith.
    split; auto with zarith.
    apply (Pos2Z.pos_le_pos 1 _).
    apply Pos.le_1_l.
  split; auto with zarith.
  now compute.
rewrite <- H.
apply Zmod_small.
assert (0 < Zpos p)%Z; auto with zarith.
split; auto with zarith.
apply Z.lt_trans with (63)%Z; auto with zarith.
Qed.

Local Definition phi_compare63 (x y: int) :
     match x ?= y with 
      Lt => (to_Z x < to_Z y)%Z
    | Gt => (to_Z y <  to_Z x)%Z
    | Eq => (to_Z x = to_Z y)%Z
    end.
Proof.
rewrite compare_spec.
now case Z.compare_spec.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*           Valid Memory Address                                            *)
(*                                                                           *)
(*****************************************************************************)


(** What it means to be a valid adress in memory                             **)
Definition valid61 p := (p < 61)%positive.

Definition validtc7 (l : list cube) :=
  match l with p :: nil => True | _  => False end.

Definition validtc4 l :=
  match l with 
  | p :: l1 => (c2N p < 4)%nat /\ validtc7 l1 
  | _  => False 
  end.

Definition validtc3 l :=
  match l with 
    cons p l1 => (c2N p < 3)%nat /\ validtc4 l1 
  | _  => False end.

Definition validto1 (l : list orientation) := length l = 1%nat.

Definition validto2 (l : list orientation) := length l = 2%nat.

Definition validto3 (l : list orientation) := length l = 3%nat.

Definition validto4 (l : list orientation) := length l = 4%nat.

Definition validto5 (l : list orientation) := length l = 5%nat.

Definition validto6 (l : list orientation) := length l = 6%nat.

Lemma validtc7_inv l :
 validtc7 l ->
 exists p1, l = p1 :: nil /\
                      (p1 = C1 \/ p1 = C2 \/ p1 = C3 \/ p1 = C4 \/
                       p1 = C5 \/ p1 = C6 \/ p1 = C7).
Proof.
case l; clear l; try (intros HH; case HH; fail).
intros c l1; case l1; simpl; auto.
2: intros c1 l2 H; case H.
intros _; exists c; split; auto.
case c; auto; do 3 (right; auto).
Qed.

Lemma validtc4_inv l : validtc4 l ->
 exists p1, exists l1, l = p1 :: l1 /\
                      (p1 = C1 \/ p1 = C2 \/ p1 = C3 \/ p1 = C4) /\
                      (validtc7 l1)%Z.
Proof.
case l; clear l; try (intros HH; case HH; fail).
intros p1 l1 [Hp1 Hl1]; exists p1; exists l1; split; auto.
generalize Hp1; case p1; simpl; auto;
 intros HH; contradict HH; apply lt_not_le; auto with arith.
Qed.

Lemma validtc3_inv l : validtc3 l ->
 exists p1, exists l1, l = p1 :: l1 /\
                      (p1 = C1 \/ p1 = C2 \/ p1 = C3) /\ (validtc4 l1)%Z.
Proof.
case l; clear l; try (intros HH; case HH; fail).
intros p1 l1 [Hp1 Hl1]; exists p1; exists l1; split; auto.
generalize Hp1; case p1; simpl; auto;
 intros HH; contradict HH; apply lt_not_le; auto with arith.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*           Correction of insertion                                         *)
(*                                                                           *)
(*****************************************************************************)

(* int63i is correct *)
Lemma spec_int63i s p : (Zpos p <= 63)%Z ->
   (to_Z s/2^(Zpos p - 1) mod 2 = if int63i s p then 1 else 0)%Z.
Proof.
intro H; unfold int63i.
case (phi_to_Z s); intros Hs1 Hs2.
assert (F1: (to_Z 1 <= 63)%Z).
  rewrite phi1; intros HH; discriminate.
assert (F2: (to_Z (shiftr63 (shiftr63 s (p2t63 p)) 1) = to_Z s / 2 ^ (Zpos p))%Z).
  repeat (rewrite phi_shiftr63; auto); rewrite phi_p2t63; auto with zarith.
  rewrite Zdiv_Zdiv; auto with zarith.
  rewrite <- Zpower_exp; try rewrite phi1; auto with zarith.
    replace (Zpos p - 1 + 1)%Z with (Zpos p); auto with zarith.
  assert (0 < Zpos p)%Z; auto with zarith; red; auto.
assert (F3: (to_Z (shiftr63 (shiftr63 s (p2t63 p)) 1) * 2 ^ to_Z 1 < 2 ^ 63)%Z).
  rewrite phi1; rewrite F2; rewrite Zpow_facts.Zpower_1_r.
  change (2^63)%Z with (2^62 * 2)%Z.
  apply Zmult_lt_compat_r; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  apply Z.lt_le_trans with (1 := Hs2).
  change (2 ^ 63)%Z with (2 ^ 62 * 2 ^ 1)%Z.
  apply Zmult_le_compat_l; auto with zarith.
  apply Zpow_facts.Zpower_le_monotone; auto with zarith.
  split; auto with zarith.
  assert (0 < Zpos p)%Z; auto with zarith; red; auto.
assert (F4: (to_Z (p2t63 p) <= 63)%Z).
  rewrite phi_p2t63; auto with zarith.
assert (F5: (2 ^ Zpos p = 2 ^ (Zpos p - 1) * 2)%Z).
  assert (FF: (0 < Zpos p)%Z); try (red; auto; fail).
  replace (2 ^ (Zpos p))%Z with (2 ^ (Zpos p -1 + 1))%Z.
  rewrite Zpower_exp; auto with zarith.
  apply f_equal2 with (f := Zpower); auto with zarith.
match goal with |- context[?X ?= ?Y] => 
  generalize (phi_compare63 X Y); case compare
end; rewrite phi_shiftl63; auto; rewrite F2; rewrite phi_shiftr63; auto;
  rewrite phi1; rewrite Zpow_facts.Zpower_1_r; rewrite phi_p2t63; auto;
  set (u := (to_Z s/ (2 ^ (Zpos p - 1)))%Z); pattern u at 1; 
  rewrite (Z_div_mod_eq u 2%Z); auto with zarith; unfold u; rewrite Zdiv_Zdiv; 
  auto with zarith; replace (2 ^ (Zpos p - 1) * 2)%Z with (2 ^(Zpos p))%Z; auto with zarith;
  rewrite Zmult_comm; fold u; case (Z_mod_lt u 2); auto with zarith.
Qed.

Lemma int63ai s p : (Zpos p <= 63)%Z ->
  int63i s p = false -> int63i (int63a s p) p = true.
Proof.
intros H H1.
assert (F0: (0 < Zpos p)%Z); try (red; auto; fail).
assert (F1: (0 < 2 ^ (Zpos p - 1))%Z); auto with zarith.
case (phi_to_Z s); intros Hs1 Hs2.
generalize (spec_int63i s p H); rewrite H1; intros H2.
generalize (spec_int63i (int63a s p) p H).
case int63i; auto.
unfold int63a.
rewrite phi_add; rewrite phi_shiftl63; rewrite phi_p2t63; 
  try (rewrite phi1; rewrite Zmult_1_l); auto with zarith.
2: apply Zpow_facts.Zpower_lt_monotone; auto with zarith.
rewrite (fun x => Zmod_small x (2^63)%Z).
- generalize (Z_div_plus_full (to_Z s) 1%Z (2 ^ (Zpos p - 1))%Z).
  rewrite Zmult_1_l; intros HH; rewrite HH; clear HH; auto with zarith.
  rewrite Zplus_mod; rewrite H2; rewrite Zplus_0_l; repeat rewrite Zmod_small;
  auto with zarith.
- split; auto with zarith.
  replace (to_Z s) with (2^(Zpos p) * (to_Z s / 2 ^ (Zpos p)) + (to_Z s mod (2^ (Zpos p - 1))))%Z.
  + apply Z.lt_le_trans with (2 ^ Zpos p * (to_Z s / 2 ^ Zpos p) + 2 ^ Zpos p)%Z.
    rewrite <- Zplus_assoc; apply Zplus_lt_compat_l.
    apply Z.le_lt_trans with (2 ^ (Zpos p - 1) - 1 + 2 ^ (Zpos p - 1))%Z.
    * apply Zplus_le_compat_r.
      case (Z_mod_lt (to_Z s) (2 ^ (Zpos p - 1))); auto with zarith.
    * replace (2 ^Zpos p)%Z with (2^(Zpos p -1) * 2 ^1)%Z.
      -- rewrite Zpow_facts.Zpower_1_r; auto with zarith.
      -- rewrite <- Zpower_exp; auto with zarith; apply f_equal2 with (f := Zpower); auto with zarith.
    * replace (2 ^ Zpos p * (to_Z s / 2 ^ Zpos p) + 2 ^ Zpos p)%Z with
           (2 ^ Zpos p * (to_Z s / 2 ^ Zpos p + 1))%Z; try ring.
      replace (2 ^ 63)%Z with (2 ^ (Zpos p) * (2^ (63 - Zpos p)))%Z.
      -- apply Zmult_le_compat_l; auto with zarith.
         assert (to_Z s / 2 ^ Zpos p < 2 ^ (63 - Zpos p))%Z; auto with zarith.
         apply Zdiv_lt_upper_bound; auto with zarith.
         rewrite <- Zpower_exp; auto with zarith.
         replace (63 - Zpos p + Zpos p)%Z with 63%Z; auto; ring.
      -- rewrite <- Zpower_exp; auto with zarith.
         apply f_equal2 with (f := Zpower); auto; ring.
  + apply sym_equal.
    pattern (to_Z s) at 1; rewrite (Z_div_mod_eq (to_Z s) (2 ^ Zpos p)%Z).
    * apply f_equal2 with (f := Zplus); auto.
      pattern (to_Z s) at 1; rewrite (Z_div_mod_eq (to_Z s) (2 ^ (Zpos p - 1))%Z).
      -- rewrite Zplus_mod.
         replace (2 ^(Zpos p))%Z with (2^(Zpos p - 1) * (2 ^ 1))%Z.
         ++ rewrite Zmult_mod_distr_l; rewrite Zpow_facts.Zpower_1_r; rewrite H2.
            rewrite Zmult_0_r; rewrite Zplus_0_l.
            rewrite Zmod_mod; apply Zmod_small.
            case (Z_mod_lt (to_Z s) (2 ^ (Zpos p - 1))%Z); auto with zarith.
         ++ rewrite <- Zpower_exp; auto with zarith.
            apply f_equal2 with (f := Zpower); auto with zarith.
      -- apply Z.lt_gt; apply Zpow_facts.Zpower_gt_0; auto with zarith.
    * apply Z.lt_gt; apply Zpow_facts.Zpower_gt_0; auto with zarith.
Qed.

Lemma int63aif s p q : (Zpos p <= 63)%Z -> (Zpos q <= 63)%Z ->
  int63i s p = false -> p <> q -> int63i (int63a s p) q = int63i s q.
Proof.
intros Hp Hq H Hd.
assert (F0: (0 < Zpos p)%Z); try (red; auto; fail).
assert (F1: (0 < 2 ^ (Zpos p - 1))%Z).
  now apply Z.pow_pos_nonneg; auto with zarith.
assert (F2: (0 < Zpos q)%Z); try (red; auto; fail).
assert (F3: (0 < 2 ^ (Zpos q - 1))%Z).
  now apply Z.pow_pos_nonneg; auto with zarith.
generalize (spec_int63i s p Hp); rewrite H; intros H1.
case (phi_to_Z s); intros Hs1 Hs2.
generalize (spec_int63i s q Hq) (spec_int63i (int63a s p) q Hq).
replace ((to_Z s / 2 ^ (Zpos q - 1)) mod 2)%Z with
        ((to_Z (int63a s p) / 2 ^ (Zpos q - 1)) mod 2)%Z.
  now intros HH; rewrite HH; case int63i; case int63i; auto;
      intros; discriminate.
unfold int63a.
rewrite phi_add; rewrite phi_shiftl63; rewrite phi_p2t63; 
  try (rewrite phi1; rewrite Zmult_1_l); auto with zarith.
2: apply Zpow_facts.Zpower_lt_monotone; auto with zarith.
assert (F : (to_Z s = 2 ^ (Zpos p) * (to_Z s / 2 ^ (Zpos p)) + 
                     (to_Z s mod (2^ (Zpos p - 1))))%Z).
  pattern (to_Z s) at 1; rewrite (Z_div_mod_eq (to_Z s) (2 ^ Zpos p)%Z).
    apply f_equal2 with (f := Zplus); auto.
    pattern (to_Z s) at 1; rewrite (Z_div_mod_eq (to_Z s) (2 ^ (Zpos p - 1))%Z).
      rewrite Zplus_mod.
      replace (2 ^(Zpos p))%Z with (2^(Zpos p - 1) * (2 ^ 1))%Z.
        rewrite Zmult_mod_distr_l; rewrite Zpow_facts.Zpower_1_r; rewrite H1.
        rewrite Zmult_0_r; rewrite Zplus_0_l.
        rewrite Zmod_mod; apply Zmod_small.
        now case (Z_mod_lt (to_Z s) (2 ^ (Zpos p - 1))%Z); auto with zarith.
      rewrite <- Zpower_exp; auto with zarith.
      now apply f_equal2 with (f := Zpower); auto with zarith.
    now apply Z.lt_gt; apply Zpow_facts.Zpower_gt_0; auto with zarith.
  now apply Z.lt_gt; apply Zpow_facts.Zpower_gt_0; auto with zarith.
rewrite (fun x => Zmod_small x (2 ^ 63)%Z).
  case (Zle_or_lt (Zpos p) (Zpos q)); intros H2.
    case (Zle_lt_or_eq _ _ H2); clear H2; intros H2.
      replace (2 ^ (Zpos q - 1))%Z with (2^(Zpos p + (Zpos q - Zpos p -1)))%Z.
        rewrite Zpower_exp; try rewrite <- Zdiv_Zdiv; auto with zarith.
        pattern (to_Z s) at 1; rewrite F.
        rewrite <- Zplus_assoc; rewrite Zplus_comm; rewrite Zmult_comm.
        rewrite Z_div_plus_full; auto with zarith.
          rewrite (Zdiv_small (to_Z s mod 2 ^ (Zpos p - 1) 
                    + 2 ^ (Zpos p - 1))%Z); auto with zarith.
            now rewrite Zplus_0_l; rewrite Zdiv_Zdiv; auto with zarith.
          case (Z_mod_lt (to_Z s) (2^(Zpos p - 1))%Z); auto with zarith;
              intros Hm1 Hm2.
          split; auto with zarith.
          replace (2 ^ Zpos p)%Z with (2^1 * (2 ^ (Zpos p - 1)))%Z.
            now rewrite Zpow_facts.Zpower_1_r; auto with zarith.
          now rewrite <- Zpower_exp; auto with zarith; 
              apply f_equal2 with (f := Zpower); auto with zarith.
      now apply f_equal2 with (f := Zpower); auto with zarith.
    now case Hd; injection H2; auto.
  replace (2 ^ (Zpos p - 1))%Z with (2 ^ (Zpos p - Zpos q) * 2 ^ (Zpos q - 1))%Z.
  2: rewrite <- Zpower_exp; auto with zarith.
  2: now apply f_equal2 with (f := Zpower); auto with zarith.
  rewrite Z_div_plus_full; auto with zarith.
  rewrite Zplus_mod.
  replace (2 ^ (Zpos p - Zpos q) mod 2)%Z with 0%Z.
    now rewrite Zplus_0_r; apply Zmod_mod; auto.
  replace (Zpos p - Zpos q)%Z with (1 + (Zpos p - Zpos q - 1))%Z; try ring.
  rewrite Zpower_exp; auto with zarith.
  now rewrite Zpow_facts.Zpower_1_r; rewrite Zmult_comm; 
      rewrite Z_mod_mult; auto.
split; auto with zarith.
rewrite F.
apply Z.lt_le_trans with (2 ^ Zpos p * (to_Z s / 2 ^ Zpos p) + 2 ^ Zpos p)%Z.
  rewrite <- Zplus_assoc; apply Zplus_lt_compat_l.
  apply Z.le_lt_trans with (2 ^ (Zpos p - 1) - 1 + 2 ^ (Zpos p - 1))%Z.
    apply Zplus_le_compat_r.
    now case (Z_mod_lt (to_Z s) (2 ^ (Zpos p - 1))); auto with zarith.
  replace (2 ^Zpos p)%Z with (2^(Zpos p -1) * 2 ^1)%Z.
    now rewrite Zpow_facts.Zpower_1_r; auto with zarith.
  now rewrite <- Zpower_exp; auto with zarith; apply f_equal2 with (f := Zpower); 
      auto with zarith.
replace (2 ^ Zpos p * (to_Z s / 2 ^ Zpos p) + 2 ^ Zpos p)%Z with
        (2 ^ Zpos p * (to_Z s / 2 ^ Zpos p + 1))%Z; try ring.
replace (2 ^63)%Z with (2 ^ (Zpos p) * (2^(63 - Zpos p)))%Z.
  apply Zmult_le_compat_l; auto with zarith.
  assert (to_Z s / 2 ^ Zpos p < 2 ^ (63 - Zpos p))%Z; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  rewrite <- Zpower_exp; auto with zarith.
  now replace (63 - Zpos p + Zpos p)%Z with 63%Z; auto; ring.
rewrite <- Zpower_exp; auto with zarith.
apply f_equal2 with (f := Zpower); auto; ring.
Qed.

Lemma int_0: forall p, (Zpos p < 61)%Z -> int63i 0 p = false.
Proof.
intros p Hp.
generalize (spec_int63i 0 p).
rewrite phi0; rewrite Zdiv_0_l; rewrite Zmod_0_l.
case int63i; auto; intros HH2.
absurd (0 = 1)%Z; auto with zarith.
Qed.

Lemma tc7ai: forall s l p, validtc7 l -> valid61 p ->
  tc7i l s p = false -> tc7i l (tc7a l s p) p = true.
Proof.
intros s l p H Hp.
assert (Hp1: (Zpos p < 61)%Z); auto.
case (validtc7_inv _ H); clear H.
intros p1 [H1 [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | H2]]]]]]]; rewrite H1 , H2;
  case s; simpl; intros; apply int63ai; auto with zarith; apply int_0; auto.
Qed.

Lemma tc7aif: forall s l1 l2 p1 p2, validtc7 l1 -> validtc7 l2  -> 
  valid61 p1 -> valid61 p2 ->
  tc7i l1 s p1 = false -> (l1 <> l2 \/ p1 <> p2) -> tc7i l2 (tc7a l1 s p1) p2 = tc7i l2 s p2.
Proof.
intros s l1 l2 p1 p2  Hl1 Hl2 Hp1 Hp2; case (validtc7_inv _ Hl1); clear Hl1;
  case (validtc7_inv _ Hl2); clear Hl2.
assert (Hpp1: (Zpos p1 < 61)%Z); auto.
assert (Hpp2: (Zpos p2 < 61)%Z); auto.
intros c1 [H1 [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | H2]]]]]]]; rewrite H1;
  rewrite H2; clear H1 H2;
  intros c2 [H1 [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | H2]]]]]]]; rewrite H1;
    rewrite H2; clear H1 H2; case s; unfold tc7i, tc7a;
    try (intros; apply int_0; auto with zarith);
    ((intros i1 i2 i3 i4 i5 i6 i7 H1 [HH | HH]) || 
     (intros _ [HH | HH]));
    try match goal with H : ?X <> ?X |- _ => case H; trivial end;
    rewrite ?int63aif; auto with zarith;
    apply int_0; auto.
Qed.

Lemma tc4ai s l p : validtc4 l -> valid61 p ->
  tc4i l s p = false -> tc4i l (tc4a l s p) p = true.
Proof.
intros H Hp.
assert (Hp1: (Zpos p < 61)%Z); auto.
case (validtc4_inv _ H); clear H.
intros p1 [l1 [H1 [[H2 | [H2 | [H2 | H2]]] H3]]]; rewrite H1;
  rewrite H2; clear H1 H2; case s; unfold tc4i, tc4a; auto;
  intros; apply tc7ai; auto.
Qed.

Lemma tc4aif s l1 l2 p1 p2 : validtc4 l1 -> validtc4 l2  -> 
  valid61 p1 -> valid61 p2 ->
  tc4i l1 s p1 = false -> (l1 <> l2 \/ p1 <> p2) -> tc4i l2 (tc4a l1 s p1) p2 = tc4i l2 s p2.
Proof.
intros Hl1 Hl2 Hp1 Hp2; case (validtc4_inv _ Hl1); clear Hl1;
  case (validtc4_inv _ Hl2); clear Hl2.
assert (Hpp1: (Zpos p1 < 61)%Z); auto.
assert (Hpp2: (Zpos p2 < 61)%Z); auto.
intros c1 [l3 [H1 [[H2 | [H2 | [H2 | H2]]] Hp]]]; rewrite H1;
  rewrite H2; clear H1 H2; 
intros q1 [l4 [H1 [[H2 | [H2 | [H2 | H2]]] Hq]]]; rewrite H1;
  rewrite H2; clear H1 H2; case s; unfold tc4i, tc4a; auto;
  intros; rewrite tc7aif; auto;
  try (match goal with H : _ \/ _ |- _  => case H end;
       auto; intros HH; left; intros HH1; case HH; rewrite HH1; auto).
Qed.

Lemma tc3ai s l p : validtc3 l -> valid61 p ->
  tc3i l s p = false -> tc3i l (tc3a l s p) p = true.
Proof.
intros H Hp.
assert (Hp1: (Zpos p < 61)%Z); auto.
case (validtc3_inv _ H); clear H.
intros p1 [l1 [H1 [[H2 | [H2 | H2]] H3]]]; rewrite H1;
  rewrite H2; clear H1 H2; case s; unfold tc3i, tc3a; auto;
  intros; apply tc4ai; auto.
Qed.

Lemma tc3aif s l1 l2 p1 p2 : validtc3 l1 -> validtc3 l2  -> 
  valid61 p1 -> valid61 p2 ->
  tc3i l1 s p1 = false -> (l1 <> l2 \/ p1 <> p2) -> 
  tc3i l2 (tc3a l1 s p1) p2 = tc3i l2 s p2.
Proof.
intros Hl1 Hl2 Hp1 Hp2; case (validtc3_inv _ Hl1); clear Hl1;
  case (validtc3_inv _ Hl2); clear Hl2.
assert (Hpp1: (Zpos p1 < 61)%Z); auto.
assert (Hpp2: (Zpos p2 < 61)%Z); auto.
intros c1 [l3 [H1 [[H2 | [H2 | H2]] Hp]]]; rewrite H1;
  rewrite H2; clear H1 H2; 
intros q1 [l4 [H1 [[H2 | [H2 | H2]] Hq]]]; rewrite H1;
  rewrite H2; clear H1 H2; case s; unfold tc3i, tc3a; auto;
  intros; rewrite tc4aif; auto;
  try (match goal with H : _ \/ _ |- _  => case H end;
       auto; intros HH; left; intros HH1; case HH; rewrite HH1; auto).
Qed.

Lemma to1ai s l l1 p : validto1 l -> validtc3 l1 -> valid61 p ->
  to1i l s l1 p = false -> to1i l (to1a l s l1 p) l1 p = true.
Proof.
intros Hl Hl1 Hp; generalize Hl; case l; clear l Hl.
intros HH; discriminate.
intros o1 l _; case o1; case s; simpl; intros; apply tc3ai; auto.
Qed.

Lemma to1aif s l1 l2 l3 l4 p1 p2 : validto1 l1 -> validto1 l2  ->
  validtc3 l3 -> valid61 p1 -> validtc3 l4 -> valid61 p2 ->
  to1i l1 s l3 p1 = false -> (l1 <> l2 \/ l3 <> l4 \/ p1 <> p2) -> 
  to1i l2 (to1a l1 s l3 p1) l4 p2 = to1i l2 s l4 p2.
Proof.
intros Hl1 Hl2 Hl3 Hl4 Hp1 Hp2; 
  generalize Hl1; case l1; clear l1 Hl1.
intros HH; discriminate.
intros o1 l; case l; clear l.
2: intros; discriminate.
generalize Hl2; case l2; clear l2 Hl2.
intros HH; discriminate.
intros o2 l; case l; clear l.
2: intros; discriminate.
case o1; case o2; case s; unfold to1i, to1a; auto;
  intros; rewrite tc3aif; auto;
  try (match goal with H : _ \/ _ |- _  => case H end;
       auto; intros HH; left; intros HH1; case HH; rewrite HH1; auto).
Qed.

Lemma to2ai s l l1 p : validto2 l -> validtc3 l1 -> valid61 p ->
  to2i l s l1 p = false -> to2i l (to2a l s l1 p) l1 p = true.
Proof.
intros Hl Hl1 Hp; generalize Hl; case l; clear l Hl.
  now intros HH; discriminate.
intros o1 l Ho1; assert (validto1 l); auto.
  now injection Ho1; auto.
case o1; case s; simpl; intros; apply to1ai; auto.
Qed.

Lemma to2aif s l1 l2 l3 l4 p1 p2 : validto2 l1 -> validto2 l2  ->
  validtc3 l3 -> valid61 p1 -> validtc3 l4 -> valid61 p2 ->
  to2i l1 s l3 p1 = false -> (l1 <> l2 \/ l3 <> l4 \/ p1 <> p2) -> 
  to2i l2 (to2a l1 s l3 p1) l4 p2 = to2i l2 s l4 p2.
Proof.
intros Hl1 Hl2 Hl3 Hl4 Hp1 Hp2; 
  generalize Hl1; case l1; clear l1 Hl1.
  now intros HH; discriminate.
generalize Hl2; case l2; clear l2 Hl2.
  now intros HH; discriminate.
intros o2 l2 Ho2 o1 l1 Ho1.
assert (Hoo1: validto1 l1).
  now injection Ho1; auto.
assert (Hoo2: validto1 l2).
  now injection Ho2; auto.
case o1; case o2; case s; unfold to2i, to2a; auto;
  intros; rewrite to1aif; auto;
  try (match goal with H : _ \/ _ |- _  => case H end;
       auto; intros HH; left; intros HH1; case HH; rewrite HH1; auto).
Qed.

Lemma to3ai s l l1 p : validto3 l -> validtc3 l1 -> valid61 p ->
  to3i l s l1 p = false -> to3i l (to3a l s l1 p) l1 p = true.
Proof.
intros Hl Hl1 Hp; generalize Hl; case l; clear l Hl.
  now intros HH; discriminate.
intros o1 l Ho1; assert (validto2 l); auto.
  now injection Ho1; auto.
case o1; case s; simpl; intros; apply to2ai; auto.
Qed.

Lemma to3aif s l1 l2 l3 l4 p1 p2 : validto3 l1 -> validto3 l2  ->
  validtc3 l3 -> valid61 p1 -> validtc3 l4 -> valid61 p2 ->
  to3i l1 s l3 p1 = false -> (l1 <> l2 \/ l3 <> l4 \/ p1 <> p2) -> 
  to3i l2 (to3a l1 s l3 p1) l4 p2 = to3i l2 s l4 p2.
Proof.
intros Hl1 Hl2 Hl3 Hl4 Hp1 Hp2; 
  generalize Hl1; case l1; clear l1 Hl1.
  now intros HH; discriminate.
generalize Hl2; case l2; clear l2 Hl2.
  now intros HH; discriminate.
intros o2 l2 Ho2 o1 l1 Ho1.
assert (Hoo1: validto2 l1).
  now injection Ho1; auto.
assert (Hoo2: validto2 l2).
  now injection Ho2; auto.
case o1; case o2; case s; unfold to3i, to3a; auto;
  intros; rewrite to2aif; auto;
  try (match goal with H : _ \/ _ |- _  => case H end;
       auto; intros HH; left; intros HH1; case HH; rewrite HH1; auto).
Qed.

Lemma to4ai s l l1 p : validto4 l -> validtc3 l1 -> valid61 p ->
  to4i l s l1 p = false -> to4i l (to4a l s l1 p) l1 p = true.
Proof.
intros Hl Hl1 Hp; generalize Hl; case l; clear l Hl.
  now intros HH; discriminate.
intros o1 l Ho1; assert (validto3 l); auto.
  now injection Ho1; auto.
case o1; case s; simpl; intros; apply to3ai; auto.
Qed.

Lemma to4aif s l1 l2 l3 l4 p1 p2 : validto4 l1 -> validto4 l2  ->
  validtc3 l3 -> valid61 p1 -> validtc3 l4 -> valid61 p2 ->
  to4i l1 s l3 p1 = false -> (l1 <> l2 \/ l3 <> l4 \/ p1 <> p2) -> 
  to4i l2 (to4a l1 s l3 p1) l4 p2 = to4i l2 s l4 p2.
Proof.
intros Hl1 Hl2 Hl3 Hl4 Hp1 Hp2; 
  generalize Hl1; case l1; clear l1 Hl1.
  now intros HH; discriminate.
generalize Hl2; case l2; clear l2 Hl2.
  now intros HH; discriminate.
intros o2 l2 Ho2 o1 l1 Ho1.
assert (Hoo1: validto3 l1).
  now injection Ho1; auto.
assert (Hoo2: validto3 l2).
  now injection Ho2; auto.
case o1; case o2; case s; unfold to4i, to4a; auto;
  intros; rewrite to3aif; auto;
  try (match goal with H : _ \/ _ |- _  => case H end;
       auto; intros HH; left; intros HH1; case HH; rewrite HH1; auto).
Qed.

Lemma to5ai s l l1 p : validto5 l -> validtc3 l1 -> valid61 p ->
  to5i l s l1 p = false -> to5i l (to5a l s l1 p) l1 p = true.
Proof.
intros Hl Hl1 Hp; generalize Hl; case l; clear l Hl.
  now intros HH; discriminate.
intros o1 l Ho1; assert (validto4 l); auto.
  now injection Ho1; auto.
case o1; case s; simpl; intros; apply to4ai; auto.
Qed.

Lemma to5aif s l1 l2 l3 l4 p1 p2 : validto5 l1 -> validto5 l2  ->
  validtc3 l3 -> valid61 p1 -> validtc3 l4 -> valid61 p2 ->
  to5i l1 s l3 p1 = false -> (l1 <> l2 \/ l3 <> l4 \/ p1 <> p2) -> 
  to5i l2 (to5a l1 s l3 p1) l4 p2 = to5i l2 s l4 p2.
Proof.
intros Hl1 Hl2 Hl3 Hl4 Hp1 Hp2; 
  generalize Hl1; case l1; clear l1 Hl1.
  now intros HH; discriminate.
generalize Hl2; case l2; clear l2 Hl2.
  now intros HH; discriminate.
intros o2 l2 Ho2 o1 l1 Ho1.
assert (Hoo1: validto4 l1).
  now injection Ho1; auto.
assert (Hoo2: validto4 l2).
  now injection Ho2; auto.
case o1; case o2; case s; unfold to5i, to5a; auto;
  intros; rewrite to4aif; auto;
  try (match goal with H : _ \/ _ |- _  => case H end;
       auto; intros HH; left; intros HH1; case HH; rewrite HH1; auto).
Qed.

Lemma to6ai s l l1 p : validto6 l -> validtc3 l1 -> valid61 p ->
  to6i l s l1 p = false -> to6i l (to6a l s l1 p) l1 p = true.
Proof.
intros Hl Hl1 Hp; generalize Hl; case l; clear l Hl.
  now intros HH; discriminate.
intros o1 l Ho1; assert (validto5 l); auto.
  now injection Ho1; auto.
case o1; case s; simpl; intros; apply to5ai; auto.
Qed.

Lemma to6aif s l1 l2 l3 l4 p1 p2 : validto6 l1 -> validto6 l2  ->
  validtc3 l3 -> valid61 p1 -> validtc3 l4 -> valid61 p2 ->
  to6i l1 s l3 p1 = false -> (l1 <> l2 \/ l3 <> l4 \/ p1 <> p2) -> 
  to6i l2 (to6a l1 s l3 p1) l4 p2 = to6i l2 s l4 p2.
Proof.
intros Hl1 Hl2 Hl3 Hl4 Hp1 Hp2; 
  generalize Hl1; case l1; clear l1 Hl1.
  now intros HH; discriminate.
generalize Hl2; case l2; clear l2 Hl2.
  now intros HH; discriminate.
intros o2 l2 Ho2 o1 l1 Ho1.
assert (Hoo1: validto5 l1).
  now injection Ho1; auto.
assert (Hoo2: validto5 l2).
  now injection Ho2; auto.
case o1; case o2; case s; unfold to6i, to6a; auto;
  intros; rewrite to5aif; auto;
  try (match goal with H : _ \/ _ |- _  => case H end;
       auto; intros HH; left; intros HH1; case HH; rewrite HH1; auto).
Qed.

(*****************************************************************************)
(*                                                                           *)
(*           Correction of iteration                                         *)
(*                                                                           *)
(*****************************************************************************)


Section IterProof.

Variable A : Type.
Variable next : A -> list cube -> list orientation -> positive -> A.


(** we first show the equivalence of int with a naive                     **)
(** version that is easier to manipulate in proofs                          **)
Fixpoint naive_int63it_aux (m : nat) (p : positive) 
                     (c : int) (l1 : list cube) 
                     (l2 : list orientation)
                     (a : A) {struct m} :=
 let a1 := if int63i c p then next a l1 l2 p else a in
 match m with 
 | O => a1
 | S m1 => naive_int63it_aux m1 (Pos.succ p) c l1 l2 a1
 end.

Lemma naive_aux0 p c l1 l2 a :
  naive_int63it_aux 0 p c l1 l2 a = if int63i c p then next a l1 l2 p else a.
Proof. auto. Qed.

Lemma naive_auxS m p c l1 l2 a :
  naive_int63it_aux (S m) p c l1 l2 a = 
  naive_int63it_aux m (Pos.succ p) c l1 l2 
   (if int63i c p then next a l1 l2 p else a).
Proof.
unfold naive_int63it_aux; auto.
Qed.

Definition naive_int63it l1 l2 a c := naive_int63it_aux 59 1 c l1 l2 a.

Lemma phi_compare63_compat u1 u2 v1 v2 :
  to_Z u1 = to_Z u2 -> to_Z v1 = to_Z v2 ->  u1 ?= v1 = (u2 ?= v2). 
Proof.
intros Hu1 Hv1.
generalize (phi_compare63 u1 v1) (phi_compare63 u2 v2);
  do 2 case compare; auto; intros H1 H2; contradict H2;
  auto with zarith.
Qed.

Theorem int63it_naive a l1 l2 c :
  int63it _ next l1 l2 a c = naive_int63it l1 l2 a c.
Proof.
revert a l1 l2 c.
assert (F:  forall m p c c1 to6 l1 l2 a,
  (Z_of_nat m + Zpos p = 60)%Z -> 
  to_Z c1 = to_Z (shiftr63 c (p2t63 p)) ->
  to_Z to6 = to_Z (shiftr63 c (p2t63 (Pos.succ p))) ->
     int63it_aux _ next (S m) p c1 to6 l1 l2  a = naive_int63it_aux m p c l1 l2 a).
  intros m; elim m; clear m; auto.
  intros p c c1 cc2 l1 l2 a H1 H2 H3.
    unfold int63it_aux, naive_int63it_aux, int63i.
    assert (F0: (0 < Zpos p)%Z); try (red; auto; fail).
    unfold Z_of_nat in H1.
    match goal with |- context[compare ?X  ?Y] =>
         set (u := X ?= Y)
    end.
    match goal with |- context[compare ?X  ?Y] =>
         set (v := compare X Y);
         replace v with u
    end.
      now case u; auto.
    unfold u; unfold v; apply phi_compare63_compat; auto.
    repeat rewrite phi_shiftl63; rewrite phi1; auto with zarith;
    try rewrite H3; rewrite phi_shiftr63; auto with zarith;
    repeat rewrite phi_shiftr63; repeat rewrite phi_p2t63; 
    repeat rewrite Zpos_succ_morphism; repeat rewrite phi1; 
    auto with zarith.
      rewrite Zdiv_Zdiv; auto with zarith.
      rewrite <- Zpower_exp; auto with zarith.
      apply f_equal2 with (f := Zmult); auto.
      apply f_equal2 with (f := Z.div); auto.
      now apply f_equal2 with (f := Zpower); auto with zarith.
      rewrite Zdiv_Zdiv; auto with zarith.
      replace (2^63)%Z with (2^62 * 2 ^1)%Z; auto.
      apply Zmult_lt_compat_r; auto with zarith.
      rewrite <- Zpower_exp; auto with zarith.
      apply Zdiv_lt_upper_bound; auto with zarith.
      case (phi_to_Z c); intros HH1 HH2; auto.
      rewrite <- Zpower_exp; auto with zarith.
      apply Z.lt_le_trans with (2^63)%Z.
        now case (phi_to_Z c); auto with zarith.
      now apply Zpow_facts.Zpower_le_monotone; auto with zarith.
    replace (2^63)%Z with (2^62 * 2 ^1)%Z; auto.
    apply Zmult_lt_compat_r; auto with zarith.
    apply Zdiv_lt_upper_bound; auto with zarith.
    case (phi_to_Z c); intros HH1 HH2; auto.
    rewrite <- Zpower_exp; auto with zarith.
    apply Z.lt_le_trans with (2 ^ 63)%Z.
      now case (phi_to_Z c); auto with zarith.
    now apply Zpow_facts.Zpower_le_monotone; auto with zarith.
  intros m Hrec p c c1 cc2 l1 l2 a H1 H2 H3.
  assert (Hk: exists k, k = S m); try exists (S m); auto.
  case Hk; clear Hk; intros k Hk; rewrite <- Hk.
  simpl int63it_aux; rewrite Hk.
  rewrite naive_auxS.
  assert (F0: (0 < Zpos p)%Z); try (red; auto; fail).
  rewrite inj_S in H1; unfold int63i.
  match goal with |- context[compare ?X  ?Y] =>
    set (u := X ?= Y)
  end.
  match goal with |- context[compare ?X  ?Y] =>
    set (v := compare X Y);
    replace v with u
  end.
    now case u; (apply Hrec; auto; [
         rewrite Zpos_succ_morphism; auto with zarith
        |  
         repeat rewrite phi_shiftr63; try rewrite phi1; auto with zarith;
         rewrite phi_p2t63; repeat rewrite Zpos_succ_morphism; auto with zarith;
         rewrite H3; repeat rewrite phi_p2t63;
         repeat rewrite Zpos_succ_morphism; auto with zarith;
         rewrite phi_shiftr63; repeat rewrite phi_p2t63;
         repeat rewrite Zpos_succ_morphism; auto with zarith;
         rewrite Zdiv_Zdiv; auto with zarith;
         rewrite <- Zpower_exp; auto with zarith;
         apply f_equal2 with (f := Z.div); auto;
         apply f_equal2 with (f := Zpower); auto with zarith]).
  unfold u; unfold v; apply phi_compare63_compat; auto.
  repeat rewrite phi_shiftl63; rewrite phi1; auto with zarith;
  try rewrite H3; rewrite phi_shiftr63; auto with zarith;
  repeat rewrite phi_shiftr63; repeat rewrite phi_p2t63; 
  repeat rewrite Zpos_succ_morphism; repeat rewrite phi1; 
  auto with zarith.
    rewrite Zdiv_Zdiv; auto with zarith.
    rewrite <- Zpower_exp; auto with zarith.
    apply f_equal2 with (f := Zmult); auto.
    apply f_equal2 with (f := Z.div); auto.
    now apply f_equal2 with (f := Zpower); auto with zarith.
    rewrite Zdiv_Zdiv; auto with zarith.
    replace (2 ^ 63)%Z with (2 ^ 62 * 2 ^ 1)%Z; auto.
    apply Zmult_lt_compat_r; auto with zarith.
    rewrite <- Zpower_exp; auto with zarith.
    apply Zdiv_lt_upper_bound; auto with zarith.
    case (phi_to_Z c); intros HH1 HH2; auto.
    rewrite <- Zpower_exp; auto with zarith.
    apply Z.lt_le_trans with (2 ^ 63)%Z.
      now case (phi_to_Z c); auto with zarith.
    now apply Zpow_facts.Zpower_le_monotone; auto with zarith.
  replace (2 ^ 63)%Z with (2 ^ 62 * 2 ^ 1)%Z; auto.
  apply Zmult_lt_compat_r; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  case (phi_to_Z c); intros HH1 HH2; auto.
  rewrite <- Zpower_exp; auto with zarith.
  apply Z.lt_le_trans with (2 ^ 63)%Z.
    now case (phi_to_Z c); auto with zarith.
  now apply Zpow_facts.Zpower_le_monotone; auto with zarith.
intros a l1 l2 c; unfold int63it, naive_int63it.
apply F; auto with zarith.
rewrite phi_shiftr63; auto with zarith.
Qed.

End IterProof.

(** Iteration                                                                **)
Section IterProof1.

Variable A : Type.
Variable next : A -> list cube -> list orientation -> positive -> A.

Local Definition nextp s (x : list cube * list orientation * positive) :=
  let (u, p) := x in let (l1, l2) := u in next s l1 l2 p.

Definition make_list s (l1 : list cube) (l2:  list orientation)
                   (p : positive) :=  s ++ ((l1,l2,p)  :: nil).

Theorem make_list63i l1 l2 c k ll :
  In k (int63it _ make_list l1 l2 ll c) ->
   In k ll \/
   exists p, (Zpos p < 61)%Z /\ k = (l1,l2,p) /\ int63i c p = true.
Proof.
rewrite int63it_naive; 
  unfold naive_int63it; generalize l1 l2 c k ll; clear l1 l2 c k ll.
assert(F:
  forall m p l1 l2 c k ll,
  (Z_of_nat m + Zpos p = 60)%Z -> 
  In k
   (naive_int63it_aux _ make_list  m p c l1 l2 ll) ->
In k ll \/
exists p1 : positive, (Zpos p <= Zpos p1 < 61)%Z /\ 
                      k = (l1,l2,p1) /\ int63i c p1 = true).
- intros m; elim m; clear m.
  + intros p l1 l2 c k ll1 H.
    rewrite naive_aux0.
    case_eq (int63i c p); intros Heq Hf; auto.
    case (in_app_or _ _ _ Hf); auto.
    simpl In; intros [H2 | H2]; try (case H2; fail); auto.
    right; exists p; auto with zarith.
  + intros m Hrec p l1 l2 c k ll H.
    rewrite naive_auxS.
    assert (F1: (Z_of_nat  m + (Zpos (Pos.succ p)) = 60)%Z).
      rewrite <- H.
      now rewrite inj_S; rewrite Zpos_succ_morphism; auto with zarith.
    case_eq (int63i c p); intros H1.
      intros HH; case (Hrec _ _ _ _ _ _ F1 HH).
        intros HH1; case (in_app_or _ _ _ HH1); auto.
        simpl In; intros HH2; case HH2; intros HH3; auto.
          now right; exists p; split; auto with zarith.
        now case HH3; auto.
      intros [p1 [Hk1 [Hk2 Hk3]]].
      right; exists p1; split; auto with zarith.
      split; auto with zarith.
      now case Hk1; rewrite Zpos_succ_morphism; auto with zarith.
    intros HH; case (Hrec _ _ _ _ _ _ F1 HH); auto.
    intros [p1 [Hk1 [Hk2 Hk3]]].
    right; exists p1; split; auto with zarith.
    split; auto with zarith.
    case Hk1; rewrite Zpos_succ_morphism; auto with zarith.
- intros l1 l2 c k ll H.
  case (F 59%nat 1%positive l1 l2 c k ll).
  + reflexivity.
  + exact H.
  + intros HH; left; exact HH.
  + intros [p [Hp1 [Hp2 Hp3]]]; right; exists p; split.
      now case Hp1; intros _ HH1; exact HH1.
    split; assumption.
Qed.

Lemma naive_auxC m p c l1 l2 a b :
  naive_int63it_aux _ 
     (fun s l1 l2 p => s ++ (l1,l2,p) :: nil) m p c l1 l2 (a :: b) = 
  a :: naive_int63it_aux _ 
        (fun s l1 l2 p => s ++ (l1,l2,p) :: nil) m p c l1 l2 b.
Proof.
revert p c l1 l2 a b; elim m; clear m.
- intros p c l1 l2 a b; repeat rewrite naive_aux0.
  case int63i; auto.
- intros m Hrec p c l1 l2 a b.
  repeat rewrite naive_auxS.
  case int63i; simpl; auto.
Qed.

Lemma naive_auxA a1 a2 m p c l1 l2 :
  naive_int63it_aux _ 
     (fun s l1 l2 p => s ++ (l1,l2,p) :: nil) m p c l1 l2 (a1 ++ a2) = 
  a1 ++ naive_int63it_aux _ 
        (fun s l1 l2 p => s ++ (l1,l2,p) :: nil) m p c l1 l2 a2.
Proof.
elim a1; clear a1; auto.
intros hd a1 Hrec.
simpl; rewrite naive_auxC; apply f_equal2 with (f := @cons _); auto.
Qed.

Theorem make_list63irI k l1 l2 ll c :
  In k ll -> In k (int63it _ make_list l1 l2 ll c).
Proof.
intro H; rewrite int63it_naive; unfold naive_int63it;
  replace ll with (ll ++ nil); try rewrite naive_auxA; auto with datatypes.
Qed.

Theorem make_list63irA c l1 l2 ll1 ll2 :
   int63it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ int63it _ make_list l1 l2 ll2 c.
Proof.
repeat rewrite int63it_naive.
unfold naive_int63it.
rewrite naive_auxA.
reflexivity.
Qed.

Theorem make_list63ir l1 l2 c p ll :
  (Zpos p < 61)%Z -> int63i c p = true ->
  In (l1,l2,p) (int63it _ make_list l1 l2 ll c).
Proof.
rewrite int63it_naive; 
  unfold naive_int63it; generalize l1 l2 c p ll; clear l1 l2 c p ll.
assert(F:
  forall m p l1 l2 c ll p1,
  (Z_of_nat m + Zpos p = 60)%Z -> 
    (Zpos p <= Zpos p1 < 61)%Z -> int63i c p1 = true ->
  In (l1,l2,p1)
   (naive_int63it_aux _
     (fun s l1 l2 p => s ++ (l1,l2,p) :: nil) m p c l1 l2 ll)).
  intros m; elim m; clear m.
  intros p l1 l2 c ll p1 H H1 H2.
  replace p with p1.
    simpl naive_int63it_aux; rewrite H2.
    now apply in_or_app; right; auto with datatypes.
    assert (H3: (Zpos p = Zpos p1)%Z).
      now simpl in H; auto with zarith.
    now injection H3; auto.
  intros m Hrec p l1 l2 c ll p1.
  rewrite inj_S; intros H [H1 H2] H3.
  rewrite naive_auxS.
  case (Zle_lt_or_eq _ _ H1); intros H4.
    apply Hrec; auto.
      now rewrite Zpos_succ_morphism; auto with zarith.
    now rewrite Zpos_succ_morphism; auto with zarith.
  replace p with p1.
    rewrite H3.
    replace (ll ++ (l1,l2,p1) :: nil) with 
            ((ll ++ (l1,l2,p1) :: nil) ++ nil); auto with datatypes.
    rewrite naive_auxA.
    apply in_or_app; left.
    now apply in_or_app; right; auto with datatypes.
  now injection H4; auto.
intros; apply F; auto with zarith.
assert (0 < Zpos p)%Z; auto with zarith; red; auto.
Qed.

Theorem make_list63fold l1 l2 a c :
  int63it _ next l1 l2 a c =
  fold_left nextp (int63it _ make_list l1 l2 nil c) a.
Proof.
rewrite int63it_naive; unfold make_list.
  rewrite int63it_naive; unfold naive_int63it.
generalize l1 l2 a c; clear l1 l2 a c.
generalize (1%positive); elim 59%nat.
  intros p l1 l2 a c; repeat rewrite naive_aux0.
  now case int63i; auto.
intros n Hrec p l1 l2 a c.
repeat rewrite naive_auxS.
case int63i; auto.
simpl.
rewrite Hrec.
replace ((l1,l2,p) ::  nil) with (((l1,l2,p) :: nil)++nil); 
  auto with datatypes.
rewrite (naive_auxA ((l1,l2,p) :: nil)); auto.
Qed.

Theorem make_listtc7i l1 l2 c k ll :
   In k (tc7it _ make_list l1 l2 ll c) -> 
   In k ll \/(exists l3, exists p, k = (l3 ++ l1,l2,p) 
               /\ validtc7 (rev l3) /\ valid61 p 
                  /\ tc7i (rev l3) c p = true).
Proof.
revert ll; unfold tc7it; case c.
  now intros ll HH; left; assumption.
intros cc1 cc2 cc3 cc4 cc5 cc6 cc7 ll.
set (ll1 := (int63it _ make_list (C7 :: l1) l2 ll cc7)).
set (ll2 := (int63it _ make_list (C6 :: l1) l2 ll1 cc6)).
set (ll3 := (int63it _ make_list (C5 :: l1) l2 ll2 cc5)).
set (ll4 := (int63it _ make_list (C4 :: l1) l2 ll3 cc4)).
set (ll5 := (int63it _ make_list (C3 :: l1) l2 ll4 cc3)).
set (ll6 := (int63it _ make_list (C2 :: l1) l2 ll5 cc2)).
intros H.
case (make_list63i _ _ _ _ _ H); clear H; unfold ll6; intros H.
- case (make_list63i _ _ _ _ _ H); clear H; unfold ll5; intros H.
  + case (make_list63i _ _ _ _ _ H); clear H; unfold ll4; intros H.
    * case (make_list63i _ _ _ _ _ H); clear H; unfold ll3; intros H.
      -- case (make_list63i _ _ _ _ _ H); clear H; unfold ll2; intros H.
         ++ case (make_list63i _ _ _ _ _ H); clear H; unfold ll1; intros H.
            ** case (make_list63i _ _ _ _ _ H); clear H; intros H.
               --- left; assumption.
               --- case H; intros p (Hp1, (Hp2, Hp3)).
                   right; rewrite Hp2.
                   exists (C7 :: nil); exists p; split.
                     now reflexivity.
                   split.
                     now unfold validtc7, valid61, rev, app; auto.
                     now split; auto.
            ** case H; intros p (Hp1, (Hp2, Hp3)).
               right; rewrite Hp2.
               exists (C6 :: nil); exists p; split.
                 now reflexivity.
               split.
                 now unfold validtc7, valid61, rev, app; auto.
               split; auto.
         ++ case H; intros p (Hp1, (Hp2, Hp3)).
            right; rewrite Hp2.
            exists (C5 :: nil); exists p; split.
              now reflexivity.
            split.
              now unfold validtc7, valid61, rev, app; auto.
            split; auto.
      -- case H; intros p (Hp1, (Hp2, Hp3)).
         right; rewrite Hp2.
         exists (C4 :: nil); exists p; split.
           now reflexivity.
         split.
           now unfold validtc7, valid61, rev, app; auto.
         split; auto.
    * case H; intros p (Hp1, (Hp2, Hp3)).
      right; rewrite Hp2.
      exists (C3 :: nil); exists p; split.
        now reflexivity.
      split.
        now unfold validtc7, valid61, rev, app; auto.
      split; auto.
  + case H; intros p (Hp1, (Hp2, Hp3)).
    right; rewrite Hp2.
    exists (C2 :: nil); exists p; split.
      now reflexivity.
    split.
      now unfold validtc7, valid61, rev, app; auto.
    split; auto.
- case H; intros p (Hp1, (Hp2, Hp3)).
  right; rewrite Hp2.
  exists (C1 :: nil); exists p; split.
    now reflexivity.
  split.
    now unfold validtc7, valid61, rev, app; auto.
  split; auto.
Qed.

Theorem make_listtc7irA c l1 l2 ll1 ll2 :
   tc7it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ tc7it _ make_list l1 l2 ll2 c.
Proof.
case c; unfold tc7it; auto with datatypes.
intros cc1 cc2 cc3 cc4 cc5 cc6 cc7; repeat rewrite make_list63irA.
reflexivity.
Qed.

Theorem make_listtc7irI k c l1 l2 ll :
   In k ll -> In k (tc7it _ make_list l1 l2 ll c).
Proof.
intro H; replace ll with (ll ++ nil);
 try rewrite make_listtc7irA; auto with datatypes.
Qed.

Theorem make_listtc7ir l p c l1 l2 ll :
   validtc7 (rev l) -> valid61 p -> tc7i (rev l) c p = true -> 
   In (l++l1,l2,p) (tc7it _ make_list l1 l2 ll c).
Proof.
(* Hack to freeze the simplification of tc7it *)
assert (H : exists f, f = tc7it).
  now exists tc7it; auto.
case H; intros f Hf; rewrite <- Hf.
case c.
  now unfold tc7i; intros _ _ HH; discriminate.
intros cc1 cc2 cc3 cc4 cc5 cc6 cc7 HH Hp.
case (validtc7_inv _ HH); clear HH.
intros p1 (HH, HH1).
rewrite <- (rev_involutive l).
rewrite HH; simpl rev; clear HH.
case HH1; [intros HH2 | intros [HH2 | [HH2 | [HH2 | [HH2 | [HH2 | HH2]]]]]];
  rewrite HH2; clear HH1 HH2; simpl; intros HH; rewrite Hf;
  unfold tc7it.
- apply make_list63ir; auto.
- apply  make_list63irI; apply make_list63ir; auto.
- do 2 (apply  make_list63irI); apply make_list63ir; auto.
- do 3 (apply  make_list63irI); apply make_list63ir; auto.
- do 4 (apply  make_list63irI); apply make_list63ir; auto.
- do 5 (apply  make_list63irI); apply make_list63ir; auto.
- do 6 (apply  make_list63irI); apply make_list63ir; auto.
Qed.

Theorem make_listtc7fold l1 l2 a c :
  tc7it _ next l1 l2 a c =
  fold_left nextp (tc7it _ make_list l1 l2 nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3 cc4 cc5 cc6 cc7; unfold tc7it.
repeat rewrite make_list63fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_list63irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.


Theorem make_listtc4i l1 l2 c k ll :
   In k (tc4it _ make_list l1 l2 ll c) -> 
   In k ll \/(exists l3, exists p, k = (l3 ++ l1,l2,p) 
               /\ validtc4 (rev l3) /\ valid61 p 
                  /\ tc4i (rev l3) c p = true).
Proof.
revert ll; unfold tc4it; case c.
  now intros ll HH; left; assumption.
intros cc1 cc2 cc3 cc4 ll.
set (ll1 := (tc7it _ make_list (C4 :: l1) l2 ll cc4)).
set (ll2 := (tc7it _ make_list (C3 :: l1) l2 ll1 cc3)).
set (ll3 := (tc7it _ make_list (C2 :: l1) l2 ll2 cc2)).
set (ll4 := (tc7it _ make_list (C1 :: l1) l2 ll3 cc1)).
intros H.
case (make_listtc7i _ _ _ _ _ H); clear H; unfold ll4; intros H.
- case (make_listtc7i _ _ _ _ _ H); clear H; unfold ll3; intros H.
  + case (make_listtc7i _ _ _ _ _ H); clear H; unfold ll2; intros H.
    * case (make_listtc7i _ _ _ _ _ H); clear H; unfold ll1; intros H.
        now left; assumption.
      case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
      right; rewrite Hp1.
      exists (l3 ++ (C4 :: nil)); exists p; split.
        now rewrite app_ass; reflexivity.
      split.
        now rewrite rev_unit; unfold validtc4, valid61; auto.
      split; auto.
      rewrite rev_unit; unfold tc4i; exact Hp4.
    * case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
      right; rewrite Hp1.
      exists (l3 ++ (C3 :: nil)); exists p; split.
        now rewrite app_ass; reflexivity.
      split.
        now rewrite rev_unit; unfold validtc4, valid61; auto.
      split; auto.
      rewrite rev_unit; unfold tc4i; exact Hp4.
  + case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
    right; rewrite Hp1.
    exists (l3 ++ (C2 :: nil)); exists p; split.
      now rewrite app_ass; reflexivity.
    split.
      now rewrite rev_unit; unfold validtc4, valid61; auto.
    split; auto.
    rewrite rev_unit; unfold tc4i; exact Hp4.
- case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
  right; rewrite Hp1.
  exists (l3 ++ (C1 :: nil)); exists p; split.
    rewrite app_ass; reflexivity.
  rewrite rev_unit; auto.
  split; auto; split; auto.
Qed.

Theorem make_listtc4irA c l1 l2 ll1 ll2 :
   tc4it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ tc4it _ make_list l1 l2 ll2 c.
Proof.
case c; unfold tc4it; auto with datatypes.
intros cc1 cc2 cc3 cc4; repeat rewrite make_listtc7irA; auto.
Qed.

Theorem make_listtc4irI k c l1 l2 ll :
   In k ll -> In k (tc4it _ make_list l1 l2 ll c).
Proof.
intro H; replace ll with (ll ++ nil);
 try rewrite make_listtc4irA; auto with datatypes.
Qed.

Theorem make_listtc4ir l p c l1 l2 ll :
   validtc4 (rev l) ->  valid61 p -> tc4i (rev l) c p = true -> 
   In (l++l1,l2,p) (tc4it _ make_list l1 l2 ll c).
Proof.
case c.
  now unfold tc4i; intros _ _ HH; discriminate.
intros cc1 cc2 cc3 cc4 HH Hp.
case (validtc4_inv _ HH); clear HH.
intros p1 (l3, (HH, (HH1, Hl3))).
rewrite <- (rev_involutive l).
rewrite HH; simpl rev; clear HH.
rewrite rev_unit; rewrite rev_involutive;
case HH1; [intros HH2 | intros [HH2 | [HH2 | HH2]]];
  rewrite HH2; clear HH1 HH2; simpl; intros HH;
  rewrite app_ass; simpl app.
- apply  make_listtc7ir; auto; rewrite rev_involutive; auto.
- apply  make_listtc7irI; apply make_listtc7ir; auto; rewrite rev_involutive; auto.
- do 2 (apply  make_listtc7irI); 
        apply make_listtc7ir; auto; rewrite rev_involutive; auto.
- do 3 (apply  make_listtc7irI); 
        apply make_listtc7ir; auto; rewrite rev_involutive; auto.
Qed.

Theorem make_listtc4fold l1 l2 a c :
  tc4it _ next l1 l2 a c =
  fold_left nextp (tc4it _ make_list l1 l2 nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3 cc4; unfold tc4it.
repeat rewrite make_listtc7fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_listtc7irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.

Theorem make_listtc3i l1 l2 c k ll :
   In k (tc3it _ make_list l1 l2 ll c) -> 
   In k ll \/(exists l3, exists p, k = (l3 ++ l1,l2,p) 
               /\ validtc3 (rev l3) /\ valid61 p 
                  /\ tc3i (rev l3) c p = true).
Proof.
revert ll; unfold tc3it; case c.
  now intros ll HH; left; assumption.
intros cc1 cc2 cc3 ll.
set (ll1 := (tc4it _ make_list (C4 :: l1) l2 ll cc3)).
set (ll2 := (tc4it _ make_list (C3 :: l1) l2 ll1 cc2)).
set (ll3 := (tc4it _ make_list (C2 :: l1) l2 ll2 cc1)).
intros H.
- case (make_listtc4i _ _ _ _ _ H); clear H; unfold ll3; intros H.
  + case (make_listtc4i _ _ _ _ _ H); clear H; unfold ll2; intros H.
    * case (make_listtc4i _ _ _ _ _ H); clear H; unfold ll1; intros H.
        now left; assumption.
      case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
      right; rewrite Hp1.
      exists (l3 ++ (C3 :: nil)); exists p; split.
        now rewrite app_ass; reflexivity.
      split.
        now rewrite rev_unit; unfold validtc3, valid61; auto.
      split; auto.
      rewrite rev_unit; unfold tc3i; exact Hp4.
    * case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
      right; rewrite Hp1.
      exists (l3 ++ (C2 :: nil)); exists p; split.
        now rewrite app_ass; reflexivity.
      split.
        now rewrite rev_unit; unfold validtc3, valid61; auto.
      split; auto.
      rewrite rev_unit; unfold tc3i; exact Hp4.
  + case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
    right; rewrite Hp1.
    exists (l3 ++ (C1 :: nil)); exists p; split.
      now rewrite app_ass; reflexivity.
    split.
      now rewrite rev_unit; unfold validtc3, valid61; auto.
    split; auto.
    rewrite rev_unit; unfold tc3i; exact Hp4.
Qed.

Theorem make_listtc3irA c l1 l2 ll1 ll2 :
   tc3it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ tc3it _ make_list l1 l2 ll2 c.
Proof.
case c; unfold tc3it; auto with datatypes.
intros cc1 cc2 cc3; repeat rewrite make_listtc4irA; auto.
Qed.

Theorem make_listtc3irI k c l1 l2 ll :
   In k ll -> In k (tc3it _ make_list l1 l2 ll c).
Proof.
intro H; replace ll with (ll ++ nil);
 try rewrite make_listtc3irA; auto with datatypes.
Qed.

Theorem make_listtc3ir l p c l1 l2 ll :
   validtc3 (rev l) ->  valid61 p -> tc3i (rev l) c p = true -> 
   In (l++l1,l2,p) (tc3it _ make_list l1 l2 ll c).
Proof.
case c.
  now unfold tc4i; intros _ _ HH; discriminate.
intros cc1 cc2 cc3 HH Hp.
case (validtc3_inv _ HH); clear HH.
intros p1 (l3, (HH, (HH1, Hl3))).
rewrite <- (rev_involutive l).
rewrite HH; simpl rev; clear HH.
rewrite rev_unit; rewrite rev_involutive;
case HH1; [intros HH2 | intros [HH2 | HH2]];
  rewrite HH2; clear HH1 HH2; simpl; intros HH;
  rewrite app_ass; simpl app.
- apply  make_listtc4ir; auto; rewrite rev_involutive; auto.
- apply  make_listtc4irI; apply make_listtc4ir; auto; rewrite rev_involutive; auto.
- do 2 (apply  make_listtc4irI); apply make_listtc4ir; auto; rewrite rev_involutive; auto.
Qed.

Theorem make_listtc3fold l1 l2 a c :
  tc3it _ next l1 l2 a c =
  fold_left nextp (tc3it _ make_list l1 l2 nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3; unfold tc3it.
repeat rewrite make_listtc4fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_listtc4irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.

Theorem make_listto1i l1 l2 c k ll :
   In k (to1it _ make_list l1 l2 ll c) -> 
   In k ll \/(exists l3, exists l4, exists p, k = (l3++l1,l4++l2,p) 
               /\ validtc3 (rev l3) /\ validto1 (rev l4) /\ valid61 p 
                  /\ to1i (rev l4) c (rev l3) p = true).
Proof.
revert ll; unfold to1it; case c.
  now intros ll HH; left; assumption.
intros cc1 cc2 cc3 ll.
set (ll1 := (tc3it _ make_list l1 (O3 :: l2) ll cc3)).
set (ll2 := (tc3it _ make_list l1 (O2 :: l2) ll1 cc2)).
set (ll3 := (tc3it _ make_list l1 (O1 :: l2) ll2 cc1)).
intros H.
case (make_listtc3i _ _ _ _ _ H); clear H; unfold ll3; intros H.
- case (make_listtc3i _ _ _ _ _ H); clear H; unfold ll2; intros H.
  + case (make_listtc3i _ _ _ _ _ H); clear H; unfold ll1; intros H.
      now left; assumption.
    case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
    right; rewrite Hp1.
    exists l3; exists (O3 :: nil); exists p; split; [auto | split; auto].
    split; [red; auto | split; auto].
  + case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
    right; rewrite Hp1.
    exists l3; exists (O2 :: nil); exists p; split; [auto | split; auto].
    split; [red; auto | split; auto].
- case H; intros l3 (p, (Hp1, (Hp2, (Hp3, Hp4)))).
  right; rewrite Hp1.
  exists l3; exists (O1 :: nil); exists p; split; [auto | split; auto].
  split; [red; auto | split; auto].
Qed.

Theorem make_listto1irA c l1 l2 ll1 ll2 :
   to1it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ to1it _ make_list l1 l2 ll2 c.
Proof.
case c; unfold to1it; auto with datatypes.
intros cc1 cc2 cc3; repeat rewrite make_listtc3irA; auto.
Qed.

Theorem make_listto1irI k c l1 l2 ll :
   In k ll -> In k (to1it _ make_list l1 l2 ll c).
Proof.
intros H; replace ll with (ll ++ nil);
 try rewrite make_listto1irA; auto with datatypes.
Qed.

Theorem make_listto1ir l1 l2 p c l3 l4 ll :
   validtc3 (rev l1) -> validto1 (rev l2) -> valid61 p -> 
   to1i (rev l2) c (rev l1) p = true -> 
   In (l1++l3,l2++l4,p) (to1it _ make_list l3 l4 ll c).
Proof.
case c.
  now unfold to1i; intros _ _ _ HH; discriminate.
intros cc1 cc2 cc3 Hl1 Hl2 Hp.
generalize Hl2; case l2; try (intros; discriminate).
simpl rev; intros o1 l5; case l5; clear l5.
2: intros o2 l5; unfold validto1; simpl rev; repeat rewrite app_length; simpl length;
   repeat rewrite <-plus_n_Sm; intros; discriminate.
simpl app; intros _; case o1; simpl; intros HH.
- apply  make_listtc3ir; auto.
- apply  make_listtc3irI; apply make_listtc3ir; auto.
- do 2 (apply  make_listtc3irI); apply make_listtc3ir; auto.
Qed.

Theorem make_listto1fold l1 l2 a c :
  to1it _ next l1 l2 a c =
  fold_left nextp (to1it _ make_list l1 l2 nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3; unfold to1it.
repeat rewrite make_listtc3fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_listtc3irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.

Theorem make_listto2i l1 l2 c k ll :
   In k (to2it _ make_list l1 l2 ll c) -> 
   In k ll \/(exists l3, exists l4, exists p, k = (l3++l1,l4++l2,p) 
               /\ validtc3 (rev l3) /\ validto2 (rev l4) /\ valid61 p 
                  /\ to2i (rev l4) c (rev l3) p = true).
Proof.
unfold to2it; case c.
  now intro HH; left; assumption.
intros cc1 cc2 cc3.
set (ll1 := (to1it _ make_list l1 (O3 :: l2) ll cc3)).
set (ll2 := (to1it _ make_list l1 (O2 :: l2) ll1 cc2)).
set (ll3 := (to1it _ make_list l1 (O1 :: l2) ll2 cc1)).
intros H.
case (make_listto1i _ _ _ _ _ H); clear H; unfold ll3; intros H.
- case (make_listto1i _ _ _ _ _ H); clear H; unfold ll2; intros H.
  + case (make_listto1i _ _ _ _ _ H); clear H; unfold ll1; intros H.
      now left; assumption.
    case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O3 :: nil)); exists p; split; [rewrite app_ass | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
  + case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O2 :: nil)); exists p; split; [rewrite app_ass | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
- case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
  right; rewrite Hp1.
  exists l3; exists (l4 ++ (O1 :: nil)); exists p; split; [rewrite app_ass | split]; 
  auto; rewrite rev_unit.
  split; [red; auto | split; auto].
  simpl; red in Hp3; rewrite Hp3; auto.
Qed.

Theorem make_listto2irA c l1 l2 ll1 ll2 :
   to2it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ to2it _ make_list l1 l2 ll2 c.
Proof.
case c; unfold to2it; auto with datatypes.
intros cc1 cc2 cc3; repeat rewrite make_listto1irA; auto.
Qed.

Theorem make_listto2irI k c l1 l2 ll :
   In k ll -> In k (to2it _ make_list l1 l2 ll c).
Proof.
intro H; replace ll with (ll ++ nil);
 try rewrite make_listto2irA; auto with datatypes.
Qed.

Theorem make_listto2ir l1 l2 p c l3 l4 ll :
   validtc3 (rev l1) -> validto2 (rev l2) -> valid61 p -> 
   to2i (rev l2) c (rev l1) p = true -> 
   In (l1++l3,l2++l4,p) (to2it _ make_list l3 l4 ll c).
Proof.
case c.
  now unfold to2i; intros _ _ _ HH; discriminate.
intros cc1 cc2 cc3 Hl1 Hl2 Hp.
pattern l2 at 2; rewrite <- (rev_involutive l2).
generalize Hl2; case (rev l2); try (intros; discriminate).
simpl rev; intros o1 l5; case o1; clear o1; intros Hl5;
  simpl; intros HH; rewrite app_ass.
- apply  make_listto1ir; auto; rewrite rev_involutive; injection Hl5; auto.
- apply  make_listto1irI; apply make_listto1ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
- do 2 (apply  make_listto1irI); apply make_listto1ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
Qed.

Theorem make_listto2fold l1 l2 a c :
  to2it _ next l1 l2 a c =
  fold_left nextp (to2it _ make_list l1 l2 nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3; unfold to2it.
repeat rewrite make_listto1fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_listto1irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.

Theorem make_listto3i l1 l2 c k ll :
   In k (to3it _ make_list l1 l2 ll c) -> 
   In k ll \/(exists l3, exists l4, exists p, k = (l3++l1,l4++l2,p) 
               /\ validtc3 (rev l3) /\ validto3 (rev l4) /\ valid61 p 
                  /\ to3i (rev l4) c (rev l3) p = true).
Proof.
unfold to3it; case c.
  now intro HH; left; assumption.
intros cc1 cc2 cc3.
set (ll1 := (to2it _ make_list l1 (O3 :: l2) ll cc3)).
set (ll2 := (to2it _ make_list l1 (O2 :: l2) ll1 cc2)).
set (ll3 := (to2it _ make_list l1 (O1 :: l2) ll2 cc1)).
intros H.
case (make_listto2i _ _ _ _ _ H); clear H; unfold ll3; intros H.
- case (make_listto2i _ _ _ _ _ H); clear H; unfold ll2; intros H.
  + case (make_listto2i _ _ _ _ _ H); clear H; unfold ll1; intros H.
      now left; assumption.
    case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O3 :: nil)); exists p; split;
      [rewrite app_ass | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
  + case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O2 :: nil)); exists p; split; [rewrite app_ass | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
- case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
  right; rewrite Hp1.
  exists l3; exists (l4 ++ (O1 :: nil)); exists p; split; [rewrite app_ass | split]; 
  auto; rewrite rev_unit.
  split; [red; auto | split; auto].
  simpl; red in Hp3; rewrite Hp3; auto.
Qed.

Theorem make_listto3irA c l1 l2 ll1 ll2 :
   to3it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ to3it _ make_list l1 l2 ll2 c.
Proof.
case c; unfold to3it; auto with datatypes.
intros cc1 cc2 cc3; repeat rewrite make_listto2irA; auto.
Qed.

Theorem make_listto3irI k c l1 l2 ll :
   In k ll -> In k (to3it _ make_list l1 l2 ll c).
Proof.
intro H; replace ll with (ll ++ nil);
 try rewrite make_listto3irA; auto with datatypes.
Qed.

Theorem make_listto3ir l1 l2 p c l3 l4 ll :
   validtc3 (rev l1) -> validto3 (rev l2) ->  valid61 p -> 
   to3i (rev l2) c (rev l1) p = true -> 
   In (l1++l3,l2++l4,p) (to3it _ make_list l3 l4 ll c).
Proof.
case c.
  now unfold to3i; intros _ _ _ HH; discriminate.
intros cc1 cc2 cc3 Hl1 Hl2 Hp.
pattern l2 at 2; rewrite <- (rev_involutive l2).
generalize Hl2; case (rev l2); try (intros; discriminate).
simpl rev; intros o1 l5; case o1; clear o1; intros Hl5;
  simpl; intros HH; rewrite app_ass.
- apply  make_listto2ir; auto; rewrite rev_involutive; injection Hl5; auto.
- apply  make_listto2irI; apply make_listto2ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
- do 2 (apply  make_listto2irI); apply make_listto2ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
Qed.

Theorem make_listto3fold l1 l2 a c :
  to3it _ next l1 l2 a c =
  fold_left nextp (to3it _ make_list l1 l2 nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3; unfold to3it.
repeat rewrite make_listto2fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_listto2irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.

Theorem make_listto4i l1 l2 c k ll :
   In k (to4it _ make_list l1 l2 ll c) -> 
   In k ll \/(exists l3, exists l4, exists p, k = (l3++l1,l4++l2,p) 
               /\ validtc3 (rev l3) /\ validto4 (rev l4) /\ valid61 p 
                  /\ to4i (rev l4) c (rev l3) p = true).
Proof.
unfold to4it; case c.
  now intros HH; left; assumption.
intros cc1 cc2 cc3.
set (ll1 := (to3it _ make_list l1 (O3 :: l2) ll cc3)).
set (ll2 := (to3it _ make_list l1 (O2 :: l2) ll1 cc2)).
set (ll3 := (to3it _ make_list l1 (O1 :: l2) ll2 cc1)).
intros H.
case (make_listto3i _ _ _ _ _ H); clear H; unfold ll3; intros H.
- case (make_listto3i _ _ _ _ _ H); clear H; unfold ll2; intros H.
  + case (make_listto3i _ _ _ _ _ H); clear H; unfold ll1; intros H.
      now left; assumption.
    case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O3 :: nil)); exists p; split; [rewrite app_ass | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
  + case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O2 :: nil)); exists p; split; [rewrite app_ass | split]; 
      auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
- case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
  right; rewrite Hp1.
  exists l3; exists (l4 ++ (O1 :: nil)); exists p; split; [rewrite app_ass | split]; 
  auto; rewrite rev_unit.
  split; [red; auto | split; auto].
  simpl; red in Hp3; rewrite Hp3; auto.
Qed.

Theorem make_listto4irA c l1 l2 ll1 ll2 :
   to4it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ to4it _ make_list l1 l2 ll2 c.
Proof.
case c; unfold to4it; auto with datatypes.
intros cc1 cc2 cc3; repeat rewrite make_listto3irA; auto.
Qed.

Theorem make_listto4irI k c l1 l2 ll :
   In k ll -> In k (to4it _ make_list l1 l2 ll c).
Proof.
intro H; replace ll with (ll ++ nil);
 try rewrite make_listto4irA; auto with datatypes.
Qed.

Theorem make_listto4ir l1 l2 p c l3 l4 ll :
   validtc3 (rev l1) -> validto4 (rev l2) -> valid61 p -> 
   to4i (rev l2) c (rev l1) p = true -> 
   In (l1++l3,l2++l4,p) (to4it _ make_list l3 l4 ll c).
Proof.
case c.
  now unfold to4i; intros _ _ _ HH; discriminate.
intros cc1 cc2 cc3 Hl1 Hl2 Hp.
pattern l2 at 2; rewrite <- (rev_involutive l2).
generalize Hl2; case (rev l2); try (intros; discriminate).
simpl rev; intros o1 l5; case o1; clear o1; intros Hl5;
  simpl; intros HH; rewrite app_ass.
- apply  make_listto3ir; auto; rewrite rev_involutive; injection Hl5; auto.
- apply  make_listto3irI; apply make_listto3ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
- do 2 (apply  make_listto3irI); apply make_listto3ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
Qed.

Theorem make_listto4fold l1 l2 a c :
  to4it _ next l1 l2 a c =
  fold_left nextp (to4it _ make_list l1 l2 nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3; unfold to4it.
repeat rewrite make_listto3fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_listto3irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.

Theorem make_listto5i l1 l2 c k ll :
   In k (to5it _ make_list l1 l2 ll c) -> 
   In k ll \/(exists l3, exists l4, exists p, k = (l3++l1,l4++l2,p) 
               /\ validtc3 (rev l3) /\ validto5 (rev l4) /\ valid61 p 
                  /\ to5i (rev l4) c (rev l3) p = true).
Proof.
unfold to5it; case c.
intros HH; left; assumption.
intros cc1 cc2 cc3.
set (ll1 := (to4it _ make_list l1 (O3 :: l2) ll cc3)).
set (ll2 := (to4it _ make_list l1 (O2 :: l2) ll1 cc2)).
set (ll3 := (to4it _ make_list l1 (O1 :: l2) ll2 cc1)).
intros H.
case (make_listto4i _ _ _ _ _ H); clear H; unfold ll3; intros H.
- case (make_listto4i _ _ _ _ _ H); clear H; unfold ll2; intros H.
  + case (make_listto4i _ _ _ _ _ H); clear H; unfold ll1; intros H.
    now left; assumption.
    case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O3 :: nil)); exists p; split; [rewrite app_ass | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
  + case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O2 :: nil)); exists p; split; [rewrite app_ass | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
- case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
  right; rewrite Hp1.
  exists l3; exists (l4 ++ (O1 :: nil)); exists p; split; [rewrite app_ass | split]; 
  auto; rewrite rev_unit.
  split; [red; auto | split; auto].
  simpl; red in Hp3; rewrite Hp3; auto.
Qed.

Theorem make_listto5irA c l1 l2 ll1 ll2 :
   to5it _ make_list l1 l2 (ll1++ll2) c =
   ll1 ++ to5it _ make_list l1 l2 ll2 c.
Proof.
case c; unfold to5it; auto with datatypes.
intros cc1 cc2 cc3; repeat rewrite make_listto4irA; auto.
Qed.

Theorem make_listto5irI k c l1 l2 ll :
   In k ll -> In k (to5it _ make_list l1 l2 ll c).
Proof.
intro H; replace ll with (ll ++ nil);
 try rewrite make_listto5irA; auto with datatypes.
Qed.

Theorem make_listto5ir l1 l2 p c l3 l4 ll :
   validtc3 (rev l1) -> validto5 (rev l2) -> valid61 p -> 
   to5i (rev l2) c (rev l1) p = true -> 
   In (l1++l3,l2++l4,p) (to5it _ make_list l3 l4 ll c).
Proof.
case c.
  now unfold to5i; intros _ _ _ HH; discriminate.
intros cc1 cc2 cc3 Hl1 Hl2 Hp.
pattern l2 at 2; rewrite <- (rev_involutive l2).
generalize Hl2; case (rev l2); try (intros; discriminate).
simpl rev; intros o1 l5; case o1; clear o1; intros Hl5;
  simpl; intros HH; rewrite app_ass.
- apply  make_listto4ir; auto; rewrite rev_involutive; injection Hl5; auto.
- apply  make_listto4irI; apply make_listto4ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
- do 2 (apply  make_listto4irI); apply make_listto4ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
Qed.

Theorem make_listto5fold l1 l2 a c :
  to5it _ next l1 l2 a c =
  fold_left nextp (to5it _ make_list l1 l2 nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3; unfold to5it.
repeat rewrite make_listto4fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_listto4irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.

Theorem make_listto6i c k ll :
   In k (to6it _ make_list ll c) -> 
   In k ll \/(exists l3, exists l4, exists p, k = (l3, l4, p) 
               /\ validtc3 (rev l3) /\ validto6 (rev l4) /\ valid61 p 
                  /\ to6i (rev l4) c (rev l3) p = true).
Proof.
unfold to6it; case c.
  now intro HH; left; assumption.
intros cc1 cc2 cc3.
set (ll1 := (to5it _ make_list nil (O3 :: nil) ll cc3)).
set (ll2 := (to5it _ make_list nil (O2 :: nil) ll1 cc2)).
set (ll3 := (to5it _ make_list nil (O1 :: nil) ll2 cc1)).
intros H.
case (make_listto5i _ _ _ _ _ H); clear H; unfold ll3; intros H.
- case (make_listto5i _ _ _ _ _ H); clear H; unfold ll2; intros H.
  + case (make_listto5i _ _ _ _ _ H); clear H; unfold ll1; intros H.
      now left; assumption.
    case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O3 :: nil)).
    exists p; split; [rewrite app_nil_r | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
  + case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
    right; rewrite Hp1.
    exists l3; exists (l4 ++ (O2 :: nil)); exists p; split; [rewrite app_nil_r | split]; 
    auto; rewrite rev_unit.
    split; [red; auto | split; auto].
    simpl; red in Hp3; rewrite Hp3; auto.
- case H; intros l3 (l4, (p, (Hp1, (Hp2, (Hp3, (Hp4, Hp5)))))).
  right; rewrite Hp1.
  exists l3; exists (l4 ++ (O1 :: nil)); exists p; split; [rewrite app_nil_r | split]; 
  auto; rewrite rev_unit.
  split; [red; auto | split; auto].
  simpl; red in Hp3; rewrite Hp3; auto.
Qed.

Theorem make_listto6irA c ll1 ll2 :
   to6it _ make_list (ll1++ll2) c =
   ll1 ++ to6it _ make_list ll2 c.
Proof.
case c; unfold to6it; auto with datatypes.
intros cc1 cc2 cc3; repeat rewrite make_listto5irA; auto.
Qed.

Theorem make_listto6irI k c ll :
   In k ll -> In k (to6it _ make_list ll c).
Proof.
intro H; replace ll with (ll ++ nil);
 try rewrite make_listto6irA; auto with datatypes.
Qed.

Theorem make_listto6ir l1 l2 p c ll :
   validtc3 (rev l1) -> validto6 (rev l2) -> valid61 p -> 
   to6i (rev l2) c (rev l1) p = true -> 
   In (l1, l2, p) (to6it _ make_list ll c).
Proof.
case c.
  now unfold to6i; intros _ _ _ HH; discriminate.
intros cc1 cc2 cc3 Hl1 Hl2 Hp.
pattern l2 at 2; rewrite <- (rev_involutive l2).
generalize Hl2; case (rev l2); try (intros; discriminate).
simpl rev; intros o1 l5; case o1; clear o1; intros Hl5;
  simpl; intros HH.
- rewrite <- (app_nil_r l1).
  apply  make_listto5ir; auto; rewrite rev_involutive; injection Hl5; auto.
- rewrite <- (app_nil_r l1).
  apply  make_listto5irI; apply make_listto5ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
- rewrite <- (app_nil_r l1).
  do 2 (apply  make_listto5irI); apply make_listto5ir; auto;
  rewrite rev_involutive; injection Hl5; auto.
Qed.

Theorem make_listto6fold a c :
  to6it _ next a c =
  fold_left nextp (to6it _ make_list nil c) a.
Proof.
case c.
  now reflexivity.
intros cc1 cc2 cc3; unfold to6it.
repeat rewrite make_listto5fold.
repeat rewrite <- fold_left_app.
repeat rewrite <- app_ass.
repeat rewrite <- make_listto5irA.
repeat rewrite <- app_nil_end.
reflexivity.
Qed.

End IterProof1.

(*****************************************************************************)
(*                                                                           *)
(*           Correction of the check                                         *)
(*                                                                           *)
(*****************************************************************************)

Lemma check63_all c : int63all c = true -> 
  forall s, (Zpos s < 61)%Z -> int63i c s = true.
Proof.
unfold int63all.
generalize (phi_compare63 c 1152921504606846975); case compare;
  try (intros; discriminate).
intros H1 _ s Hs.
assert (F0: (Zpos s <= 63)%Z); auto with zarith.
generalize (spec_int63i c s F0); rewrite H1.
case int63i; auto.
change (to_Z 1152921504606846975)%Z with (1152921504606846975)%Z.
generalize s Hs; clear s Hs F0.
do 5 (intros s; case s; clear s;
      [idtac|idtac| match goal with |- context[?X = 0%Z] =>
                     change X with 1%Z end;
                     intros; discriminate]);
try (intros p; case p; [intros p1 HH | intros p1 HH | intros HH]; 
  try (discriminate HH));
(match goal with |- context[?X = 0%Z] =>
                     change X with 1%Z end;
                     intros HH1; discriminate HH1).
Qed.

Lemma checktc7_all : forall c, tc7all c = true -> 
  forall l p, validtc7 l -> valid61 p -> tc7i l c p = true.
Proof.
intros c; case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 p4 p5 p6 p7 Hc l p Hl; simpl in Hc; generalize Hc;
  clear Hc; case (validtc7_inv _ Hl).
intros c1 (Hc1, [H2 | [H2 |  [H2 | [H2 | [H2 | [H2 | H2]]]]]]); 
  rewrite Hc1; rewrite H2; unfold tc7i;
  intros Ha Hp;
  match goal with |-  int63i ?X  _ = _ => 
    apply (fun x => check63_all X x _ Hp); generalize Ha
  end;  do 7 (case int63all; auto).
Qed.

Lemma checktc4_all c l p : tc4all c = true -> 
  validtc4 l -> valid61 p -> tc4i l c p = true.
Proof.
case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 p4 Hc Hl; simpl in Hc; generalize Hc;
  clear Hc; case (validtc4_inv _ Hl).
intros c1 (l1, (Hl1, [[H2 | [H2 | [H2 | H2]]] Hl2]));
  rewrite Hl1; rewrite H2; unfold tc4i;
  intros Hp; apply checktc7_all; auto;
  generalize Hp; do 4 (case tc7all; auto).
Qed.

Lemma checktc3_all c l p : tc3all c = true -> 
  validtc3 l -> valid61 p -> tc3i l c p = true.
Proof.
case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 Hc Hl; simpl in Hc; generalize Hc;
  clear Hc; case (validtc3_inv _ Hl).
intros c1 [l1 [Hl1 [[H2 | [H2 | H2]] Hl2]]];
  rewrite Hl1; rewrite H2; unfold tc3i;
  intros Hp; apply checktc4_all; auto;
  generalize Hp; do 3 (case tc4all; auto).
Qed.

Lemma checkto1_all c l1 l2 p : to1all c = true -> 
  validtc3 l1 -> validto1 l2 -> valid61 p ->
  to1i l2 c l1 p = true.
Proof.
case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 Hc Hl; simpl in Hc; generalize Hc;
  clear Hc.
case l2; try (intros; discriminate); clear l2.
intros o1 l2; case l2; try (intros; discriminate).
case o1; unfold to1i; intros; apply checktc3_all; auto;
  generalize Hc; do 3 (case tc3all; auto).
Qed.

Lemma checkto2_all c l1 l2 p : to2all c = true -> 
  validtc3 l1 -> validto2 l2 -> valid61 p ->
  to2i l2 c l1 p = true.
Proof.
case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 Hc Hl; simpl in Hc; generalize Hc;
  clear Hc.
case l2; try (intros; discriminate); clear l2.
intros o1 l2 Hc Hl2; assert (Hl3: validto1 l2); auto.
  now injection Hl2; auto.
case o1; unfold to1i; intros; apply checkto1_all; auto;
  generalize Hc; do 3 (case to1all; auto).
Qed.

Lemma checkto3_all c l1 l2 p : to3all c = true -> 
  validtc3 l1 -> validto3 l2 -> valid61 p ->
  to3i l2 c l1 p = true.
Proof.
case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 Hc Hl; simpl in Hc; generalize Hc;
  clear Hc.
case l2; try (intros; discriminate); clear l2.
intros o1 l2 Hc Hl2; assert (Hl3: validto2 l2); auto.
  now injection Hl2; auto.
case o1; unfold to2i; intros; apply checkto2_all; auto;
  generalize Hc; do 3 (case to2all; auto).
Qed.

Lemma checkto4_all c l1 l2 p : to4all c = true -> 
  validtc3 l1 -> validto4 l2 -> valid61 p ->
  to4i l2 c l1 p = true.
Proof.
case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 Hc Hl; simpl in Hc; generalize Hc;
  clear Hc.
case l2; try (intros; discriminate); clear l2.
intros o1 l2 Hc Hl2; assert (Hl3: validto3 l2); auto.
  now injection Hl2; auto.
case o1; unfold to2i; intros; apply checkto3_all; auto;
  generalize Hc; do 3 (case to3all; auto).
Qed.

Lemma checkto5_all c l1 l2 p : to5all c = true -> 
  validtc3 l1 -> validto5 l2 -> valid61 p ->
  to5i l2 c l1 p = true.
Proof.
case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 Hc Hl; simpl in Hc; generalize Hc;
  clear Hc.
case l2; try (intros; discriminate); clear l2.
intros o1 l2 Hc Hl2; assert (Hl3: validto4 l2); auto.
  now injection Hl2; auto.
case o1; unfold to2i; intros; apply checkto4_all; auto;
  generalize Hc; do 3 (case to4all; auto).
Qed.

Lemma checkto6_all c l1 l2 p : to6all c = true -> 
  validtc3 l1 -> validto6 l2 -> valid61 p ->
  to6i l2 c l1 p = true.
Proof.
case c; [intros HH; discriminate | idtac].
intros p1 p2 p3 Hc Hl; simpl in Hc; generalize Hc;
  clear Hc.
case l2; try (intros; discriminate); clear l2.
intros o1 l2 Hc Hl2; assert (Hl3: validto5 l2); auto.
  now injection Hl2; auto.
case o1; unfold to2i; intros; apply checkto5_all; auto;
  generalize Hc; do 3 (case to5all; auto).
Qed.


(*****************************************************************************)
(*                                                                           *)
(*           Correction of encoding/decoding                                 *)
(*                                                                           *)
(*****************************************************************************)

Lemma encode_aux_length p l : length (encode_aux l p) = length l.
Proof. elim l; simpl; auto. Qed.

Lemma encode_length n l : 
  (length l <= n)%nat -> length (encode l n) = length l.
Proof.
revert l; elim n; simpl; auto; clear n.
  intros l; case l; auto.
  now intros p1 l1 H; inversion H.
intros n Hrec l; case l; simpl; auto.
intros p1 l1 H; rewrite Hrec; auto; 
  rewrite encode_aux_length; auto with arith.
Qed.

Lemma encode_aux_app p l1 l2 : 
  encode_aux (l1 ++ l2) p = encode_aux l1 p ++ encode_aux l2 p.
Proof.
revert l2; elim l1; simpl; auto.
intros a l3 Hrec; case cube_compare; intros l2; rewrite Hrec; auto.
Qed.

Lemma encode_aux_in_less l p q :
  (c2N q < c2N p)%nat -> ~(In p l) -> 
  In q (encode_aux l p) -> In q l.
Proof.
intros H1; elim l; simpl; auto with datatypes; clear l.
intros p1 l Hrec H2.
generalize (cube_compare_correct p p1); case cube_compare; intros HH; auto.
- case H2; auto.
- intros [HH1 | HH1]; auto.
  assert (H: (c2N q + 1 = c2N p1)%nat).
    now generalize HH HH1; case p1; case q; simpl; auto;
        try (intros; discriminate); intros HH2; contradict HH2; auto with arith.
  intros; apply False_ind; auto with zarith.
  right; apply Hrec; auto.
- intros [HH1 | HH1]; auto.
  right; apply Hrec; auto.
Qed.

Lemma encode_aux_in_more l p q : 
  (c2N q >= c2N p)%nat -> ~ (In p l) -> 
    In q (encode_aux l p) -> In (cube_succ q) l.
Proof.
intros H1; elim l; simpl; auto with datatypes; clear l.
intros p1 l Hrec H2.
assert (F0: p1 <> p); auto.
assert (F0b: ~ In p l); auto; clear H2.
generalize (cube_compare_correct p p1); case cube_compare;
 intros H3 H4; auto.
- case F0; auto.
- case H4; clear H4; auto; intros H4.
  rewrite <- H4; left; generalize H3; case p1; simpl; auto.
  intros HH; contradict HH; auto with arith.
- case H4; clear H4; auto; intros H4.
  contradict H1; rewrite <- H4; auto with zarith.
Qed.

Lemma encode_aux_unique p l :
   unique (p :: l) -> unique (encode_aux l p).
Proof.
generalize p; elim l; simpl; auto; clear p l.
  now intros; apply uniqN.
intros q l Hrec1 p Hpal.
inversion_clear Hpal as [ | xx yy Ha Hl].
inversion_clear Ha as [ | xx yy Ha1 Hl1].
apply uniqC.
  apply Hrec1; auto.
  now apply uniqC; auto with datatypes.
generalize (cube_compare_correct p q); case cube_compare; intros H1 H2.
- case Hl; rewrite H1; auto with datatypes.
- case Hl1.
  replace q with (cube_succ (cube_pred q)).
  apply encode_aux_in_more with p; auto with datatypes.
  now generalize H1; case p; case q; simpl; auto with arith.
  generalize H1; case q; auto; intros HH; contradict HH; auto with arith.
- case Hl1; apply encode_aux_in_less with p; auto with zarith datatypes.
Qed.

Lemma decode_aux_length p l : length (decode_aux l p) = length l.
Proof. elim l; simpl; auto. Qed.

Lemma decode_length l : length (decode l) = length l.
Proof.
elim l; simpl; auto; clear l.
intros p1 l1 Hrec; rewrite decode_aux_length; auto.
Qed.

Lemma decode_aux_app p l1 l2 : 
  decode_aux (l1 ++ l2) p = decode_aux l1 p ++ decode_aux l2 p.
Proof.
revert l2; elim l1; simpl; auto.
intros a l3 Hrec; case cube_compare; intros l2; rewrite Hrec; auto.
Qed.

Lemma decode_encode n l : 
  (length l <= n)%nat -> unique l -> l = decode (encode l n).
Proof.
revert l; elim n; simpl; clear n.
  intros l; case l; simpl; auto.
  now intros p1 k1 HH; inversion HH.
intros n Hrec l; case l; simpl; auto; clear l.
intros p1 l H H1; apply f_equal2 with (f := @cons _); auto.
rewrite <- Hrec.
- inversion_clear H1 as [ |xx yy Ha Hb].
  generalize Hb; elim Ha; auto; clear l Ha Hb H.
  intros a1 l Ha Hrec1 Hb Ha1.
  simpl.
  generalize (cube_compare_correct p1 a1); case cube_compare; intros H2.
  + case Ha1; rewrite H2; auto with datatypes.
  + generalize (cube_compare_correct p1 (cube_pred a1)); case cube_compare; 
       intros H3.
    * apply f_equal2 with (f := @cons _); auto with datatypes.
      generalize H2; case a1; auto; intros HH; contradict HH; auto with arith.
    * apply f_equal2 with (f := @cons _); auto with datatypes.
      generalize H2; case a1; auto; intros HH; contradict HH; auto with arith.
    * contradict H3; generalize H2; case a1; auto with arith.
  + generalize (cube_compare_correct p1 a1); case cube_compare; intros H3;
    try (contradict H2; try rewrite H3; auto with arith; fail).
    apply f_equal2 with (f := @cons _); auto with datatypes.
- rewrite encode_aux_length; auto with arith.
- apply encode_aux_unique; auto.
Qed.

Require Import Max.

Definition lmax l := fold_right (fun x y => max (c2N x) y) 0%nat l.

Lemma lmax_app l1 l2 :lmax (l1 ++ l2) = max (lmax l1) (lmax l2).
Proof.
revert l2; elim l1; simpl; clear l1; auto.
intros a l Hrec l2.
rewrite <- max_assoc; rewrite Hrec; auto.
Qed.

Lemma encode_aux_id p l :
  (lmax l < c2N p -> encode_aux l p = l)%nat.
Proof.
elim l; simpl; auto.
intros a l1 Hrec Hp.
assert (Hp1: (lmax l1 < c2N p)%nat).
  now apply le_lt_trans with (2 := Hp); auto with arith.
assert (Hp2: (c2N a < c2N p)%nat).
  now apply le_lt_trans with (2 := Hp); auto with arith.
generalize (cube_compare_correct p a); case cube_compare; intros H1.
- apply f_equal2 with (f := @cons _); auto.
- contradict H1; auto with zarith.
- apply f_equal2 with (f := @cons _); auto.
Qed.

Lemma encode_aux_lmax_le p l :
  (lmax (encode_aux l p) <= lmax l)%nat.
Proof.
elim l; simpl; auto with zarith.
intros a l1 Hrec.
generalize (cube_compare_correct p a); case cube_compare; intros H.
- apply max_case; auto with arith.
  apply le_trans with (1 := Hrec); auto with arith.
- apply max_case; auto with arith.
    apply le_trans with (c2N a); auto with arith.
    now case a; auto with arith.
  apply le_trans with (1 := Hrec); auto with arith.
- apply max_case; auto with arith.
  apply le_trans with (1 := Hrec); auto with arith.
Qed.

Lemma lmax_inv l :
 (l <> nil -> exists p, lmax l = c2N p /\ In p l)%nat.
Proof.
elim l; simpl.
  now intros HH; case HH; auto with arith.
intros c1 l1; case l1.
  intros; exists c1; split; simpl; auto.
  now rewrite max_l; auto with arith.
intros c2 l2 HH; case HH; auto.
  now intros; discriminate.
intros c3 (Hc3, Hc4); rewrite Hc3.
apply max_case.
  now intros; exists c1; auto.
intros; exists c3; auto with datatypes.
Qed.

Lemma encode_aux_lmax_lt l p :
  (l <> nil -> unique (p :: l) -> c2N p <= lmax l -> 
   lmax (encode_aux l p) < lmax l)%nat.
Proof.
revert l p.
assert (F0 : forall p l, l <> nil -> unique (p :: l) -> (c2N p <= lmax l ->
                         c2N p < lmax l)%nat).
  intros p l Hl H H1; case (le_lt_or_eq  _ _ H1); auto; intros H2.
  case (lmax_inv l); auto.
  intros q; rewrite <- H2; intros (H3, H4).
  inversion_clear H as [ | xx yy Ha Hb].
  case Hb; replace p with q; auto.
  now generalize H3; case p; case q; auto; intros; discriminate.
intros l; elim l; simpl.
  now intros p HH; case HH; auto.
intros a l1 Hrec p _ Hp.
generalize (cube_compare_correct p a); case cube_compare; intros Hp1 H1.
- inversion_clear Hp as [ | xx yy Ha Hb].
  case Hb; rewrite Hp1; auto with datatypes.
- apply max_case; auto.
    apply lt_le_trans with (c2N a); auto with arith.
    now generalize Hp1; case a; auto with arith; intros HH; contradict HH; 
        auto with arith.
  generalize Hrec Hp H1 ; case l1; auto; clear l1 Hrec Hp H1.
    simpl lmax; generalize Hp1; case a; simpl; auto with arith.
    now intros HH; contradict HH; auto with arith.
  intros a1 l2 Hrec Hp H1.
  case (le_or_lt (c2N p) (lmax (a1 :: l2))); intros H2.
    apply lt_le_trans with (lmax (a1 :: l2)); auto with arith.
    apply Hrec; auto; try (intros; discriminate).
    inversion_clear Hp as [ | xx yy Ha Hb].
    inversion_clear Ha as [ | xx1 yy1 Ha1 Hb1].
    now apply uniqC; auto with datatypes.
  apply lt_le_trans with (c2N a); auto with arith.
  apply le_lt_trans with (c2N p); auto with arith.
  apply le_trans with (lmax (a1 :: l2)); auto with arith.
  apply encode_aux_lmax_le; auto.
- assert (H2: (c2N p <= (lmax l1))%nat).
    now generalize H1 Hp1; apply max_case; auto with zarith.
  generalize Hrec Hp H2 ; case l1; auto; clear l1 Hrec Hp H1 H2.
    simpl lmax.
    now intros _ _ HH; contradict HH; auto with zarith.
  intros a1 l2 Hrec Hp H1.
  rewrite (max_r (c2N a) (lmax (a1 :: l2))); auto with zarith.
  apply max_case; auto with zarith.
  apply Hrec; auto with arith; try (intros; discriminate).
  inversion_clear Hp as [ | xx yy Ha Hb].
  inversion_clear Ha as [ | xx1 yy1 Ha1 Hb1].
  apply uniqC; auto with datatypes.
Qed.

Lemma encode_max n l a : 
  (length l  <= n)%nat -> 
   unique (l ++ (a :: nil)) -> 
   (lmax  (l ++ (a :: nil)) <= length l)%nat ->
   encode (l ++ (a :: nil)) (S n) = encode l n ++ (C1 :: nil).
Proof.
revert l a; elim n; clear n.
  intros l; case l; simpl; auto.
    intros a _ _; rewrite max_l; auto with zarith.
    intros; apply f_equal2 with (f := @cons _); auto.
    now generalize H; case a; simpl; auto with arith;
        intros HH; contradict HH; auto with arith.
  now intros p l1 a H; contradict H; auto with arith.
intros n Hrec l; case l; auto; clear l.
  intros a _ _; simpl; rewrite max_l; auto with zarith.
  now case a; simpl; auto with arith;
      intros HH; contradict HH; auto with arith.
intros p l a H1 H2 H3.
change (encode ((p :: l) ++ a :: nil) (S (S n))) with
 (p ::  encode (encode_aux (l ++ a :: nil) p) (S n)).
change (encode (p :: l) (S n) ++ C1 :: nil) with
 (p ::  (encode (encode_aux l p) n ++ C1 :: nil)).
apply f_equal2 with (f := @cons _); auto.
assert (F1: (length (l ++ a :: nil) <= S n)%nat).
  now rewrite app_length; rewrite plus_comm; auto.
generalize F1; rewrite <- (encode_aux_length p).
assert (F2: unique (encode_aux (l ++ a :: nil) p)).
  now apply encode_aux_unique; auto.
generalize F2.
rewrite encode_aux_app.
intros G1 G2.
set (u := encode_aux l p); simpl encode_aux.
apply Hrec; unfold u.
- rewrite encode_aux_length.
  apply le_S_n; generalize F1; rewrite app_length; auto.
- assert (F3: unique (encode_aux (l ++ a :: nil) p)).
    now apply encode_aux_unique; auto.
  generalize F3; rewrite encode_aux_app; auto.
- change (match cube_compare p a with
          | Eq => a
          | Lt => cube_pred a
          | Gt => a
          end :: nil) with (encode_aux (a :: nil) p).
  rewrite <- encode_aux_app.
  assert (F4:
    (lmax (encode_aux (l ++ a :: nil) p) < length (p :: l))%nat).
    case (le_or_lt (c2N p) (lmax (l ++ a :: nil))); intros H4.
      assert (F3 : (lmax (encode_aux (l ++ a :: nil) p) < lmax (l ++ a :: nil))%nat).
        apply encode_aux_lmax_lt; auto.
        now case l; intros; discriminate.
      change (lmax ((p :: l) ++ a :: nil)) with
             (max (c2N p) (lmax (l ++ a :: nil))) in H3.
      rewrite max_r in H3; auto.
      now apply lt_le_trans with (1 := F3); auto.
    rewrite encode_aux_id; auto.
    apply lt_le_trans with (2 := H3); auto.
    change (lmax ((p :: l) ++ a :: nil)) with
           (max (c2N p) (lmax (l ++ a :: nil))).
    now rewrite max_l; auto with zarith.
  rewrite encode_aux_length.
  generalize F4; unfold length; repeat rewrite inj_S; auto with zarith.
Qed.

Fixpoint decrease l m {struct l} := 
  match l with 
    nil => True
  | n ::  l1 => (c2N n < m)%nat /\ decrease l1 (Nat.pred m)
  end.

Lemma encode_decrease n m l : 
  (length l <= n)%nat -> unique l -> (lmax l < m)%nat ->
   decrease (encode l n) m.
Proof.
revert m l; elim n; simpl; clear n.
  now intros m l; case l; simpl; auto; clear l.
intros n Hrec m l; case l; simpl; auto; clear l.
intros p l H1 H2 H3.
inversion_clear H2 as [ | xx yy Ha Hb].
split; auto.
  now apply le_lt_trans with (2:= H3); apply le_max_l.
generalize H1 H3 Ha Hb; case l; clear l H1 H3 Ha Hb.
  now intros; case n; simpl; auto.
intros c l H1 H3 Ha Hb.
apply Hrec; auto.
- rewrite encode_aux_length; auto with arith.
- apply encode_aux_unique; auto.
  apply uniqC; auto.
- case (le_or_lt (c2N p) (lmax (c :: l))); intros H4.
    rewrite max_r in H3; auto with zarith.
    apply lt_le_trans with (lmax (c :: l)).
      apply encode_aux_lmax_lt; auto with arith.
        now intros HH; discriminate.
      now apply uniqC; auto.
    now generalize H3; case m; auto with arith.
  rewrite encode_aux_id; auto.
  apply lt_le_trans with (1 := H4).
  apply le_trans with (max (c2N p) (lmax (c :: l))).
    now apply le_max_l.
  generalize H3; case m; auto with arith.
Qed.

Lemma lmax_perm l1 l2 : perm l1 l2 -> lmax l1 = lmax l2.
Proof.
intro H; elim H; clear l1 l2 H; simpl; auto.
  now intros a b l; repeat rewrite max_assoc; rewrite (max_comm (c2N a)); auto.
intros l1 l2 l3 _ H1 _ H2; rewrite H1; auto.
Qed.

Local Definition list3 := (list cube * list orientation * positive)%type.

Definition rev3 (l : list3) := 
  match l with (l1,l2,p) => (rev l1, rev l2, p) end.

Definition valid3 t := 
  match t with
   (l1, l2, p) => 
      validtc3 l1 /\ validto6 l2 /\ valid61 p
  end.

Definition decode3 t := 
  match t with
   (l1, l2, p) => decode_state l1 l2 p 
  end.

Lemma encode_decode_state s :
  valid_state s -> decode3 (rev3 (encode_state s)) = s.
Proof.
assert (Har: forall n m, (m <= n -> m - n = 0)%nat).
  induction n as [ | n Hrec]; destruct m as [ | m]; simpl; auto with arith.
case s.
intros i7 i6 i5 i4 i3 i2 i1 o1 o2 o3 o4 o5 o6 o7 H.
unfold encode_state.
set (l1 := (i7 :: i6 :: i5 :: i4 :: i3 :: i2 :: i1 :: nil)).
unfold encode_memo, encode_memo_list.
rewrite memo_get_val_correct.
assert (F1: unique l1).
  case H; intros H1 H2.
  apply unique_perm with (1 := H1).
  now apply unique7.
assert (F2: lmax l1 = 6%nat).
  case H; intros H1 _.
  now unfold l1; rewrite <- (lmax_perm _ _ H1); simpl; auto.
assert (F3: (decrease (encode l1 7) 7)).
  now apply encode_decrease; auto; rewrite F2; red; auto.
generalize (decode_encode 7 l1 (le_n _) F1) F3.
change l1 with
  ((i7 :: i6 :: i5 :: i4 :: i3 :: i2 :: nil) ++ (i1 :: nil)).
rewrite encode_max; auto.
  case encode.
    now intros; discriminate.
  intros p7 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p6 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p5 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p4 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p3 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p2 l Hp; unfold rev, app, decode_state.
  match type of Hp with _ = decode ?X =>
    generalize (decode_length X); rewrite <- Hp;
    simpl length; repeat rewrite app_length;  simpl length
  end.
  generalize Hp; case l; simpl length; simpl app; clear Hp.
    intros Hp _ (Hd1, (Hd2, (Hd3, (Hd4, (Hd5, (Hd6, _)))))).
    unfold rev3, decode3; simpl rev; unfold decode_state.
    rewrite cube3_encode_decode; auto with arith.
    unfold decode_memo, decode_memo_list.
    rewrite memo_get_val_correct.
    rewrite <- Hp; simpl.
    case H; simpl; intros H1 H2.
    rewrite oinv_eq with (oy := o7); auto.
    assert (oadd_assoc: forall ox oy oz, oadd ox (oadd oy oz) = 
                                         oadd (oadd ox oy) oz).
      now intros ox oy oz; case ox; case oy; case oz; auto.
    now repeat rewrite oadd_assoc; auto.
  intros pp ll; rewrite plus_comm.
  now intros _ HH; inversion HH.
simpl app; case H; intros H1 _.
rewrite <- (lmax_perm _ _ H1); simpl; auto with arith.
Qed.

Lemma encode_valid s : valid_state s -> valid3 (encode_state s).
Proof.
case s.
intros i7 i6 i5 i4 i3 i2 i1 o1 o2 o3 o4 o5 o6 o7 H.
unfold encode_state.
set (l1 := (i7 :: i6 :: i5 :: i4 :: i3 :: i2 :: i1 :: nil)).
unfold encode_memo, encode_memo_list.
rewrite memo_get_val_correct.
assert (F1 : unique l1).
  case H; intros H1 H2.
  apply unique_perm with (1 := H1).
  now apply unique7.
assert (F2: lmax l1 = 6%nat).
  case H; intros H1 _.
  now unfold l1; rewrite <- (lmax_perm _ _ H1); simpl; auto.
assert (F3: (decrease (encode l1 7) 7)).
  now apply encode_decrease; auto; rewrite F2; red; auto.
generalize (decode_encode 7 l1 (le_n _) F1) F3.
change l1 with
  ((i7 :: i6 :: i5 :: i4 :: i3 :: i2 :: nil) ++ (i1 :: nil)).
rewrite encode_max; auto.
  case encode.
    now intros; discriminate.
  intros p7 l; case l; clear l.
    match goal with |- ?X = ?Y -> _ =>
       intros HH; assert (HH1: length X = length Y); try discriminate
    end.
  intros p6 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p5 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p4 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p3 l; case l; clear l.
    now match goal with |- ?X = ?Y -> _ =>
          intros HH; assert (HH1: length X = length Y); try discriminate
        end.
  intros p2 l Hp; unfold rev, app, decode_state.
  match type of Hp with _ = decode ?X =>
    generalize (decode_length X); rewrite <- Hp;
    simpl length; repeat rewrite app_length;  simpl length
  end.
  generalize Hp; case l; simpl length; simpl app; clear Hp.
    intros Hp _ (Hd1, (Hd2, (Hd3, (Hd4, (Hd5, (Hd6, _)))))).
    repeat split; auto.
    unfold valid61; generalize Hd2 Hd3 Hd6; 
        case p2; case p5; case p6; simpl;
        intros H1 H2 H3; red; auto;
        contradict H1; apply le_not_gt; auto with arith;
        contradict H2; apply le_not_gt; auto with arith;
        contradict H3; apply le_not_gt; auto with arith.
  intros pp ll; rewrite plus_comm.
  now intros _ HH; inversion HH.
simpl app; case H; intros H1 _.
rewrite <- (lmax_perm _ _ H1); simpl.
unfold Z.max; simpl; auto with zarith.
Qed.


(*****************************************************************************)
(*                                                                           *)
(*      Correction of the reachability by equivalence                        *)
(*       with the naive model defined in BasicRubik                          *)
(*                                                                           *)
(*****************************************************************************)


Definition cube_dec (c1 c2 : cube) : {c1 = c2} + {c1 <> c2}.
Proof.
case c1; case c2; try (right; intros; discriminate);
  left; auto.
Defined.

Definition orientation_dec (o1 o2 : orientation) : {o1 = o2} + {o1 <> o2}.
Proof.
case o1; case o2; try (right; intros; discriminate);
  left; auto.
Defined.

Lemma positive_dec (p1 p2 : positive) : {p1 = p2} + {p1 <> p2}.
Proof.
generalize (positive_eq_correct p1 p2).
case positive_eq; try (left; auto; fail); right; auto.
Defined.

Definition list3_dec (s1 s2 : list3) : {s1 = s2} + {s1 <> s2}.
Proof.
destruct s1 as ((l1,l2),p1).
destruct s2 as ((l3,l4),p2).
case (list_eq_dec cube_dec l1 l3); intros H1.
2: right; intros H2; case H1; injection H2; auto.
case (list_eq_dec orientation_dec l2 l4); intros H2.
2: right; intros H3; case H2; injection H3; auto.
case (positive_dec p1 p2); intros H3; auto.
  now left; repeat apply f_equal2 with (f := @pair _ _); auto.
right; intros H4; case H3; injection H4; auto.
Defined.

Lemma rev3_involutive s : rev3 (rev3 s) = s.
Proof.
destruct s as ((l1,l2),p); simpl; repeat rewrite rev_involutive; auto.
Qed.

Definition state_equiv s l := l = rev3 (encode_state s).

Definition states_equiv ss ll := 
   forall s,
   In s (to6it _ make_list nil ll) <->
   In s (map (fun x => rev3 (encode_state x)) ss).

Definition pstates_equiv pss pll := 
   states_equiv (fst pss) (fst pll) /\
   states_equiv (snd pss) (snd pll).

Lemma states_equiv_equiv ss1 ss2 ll :
  states_equiv ss1 ll -> lequiv ss1 ss2 -> states_equiv ss2 ll.
Proof.
unfold states_equiv, lequiv; intros H1 H2 s.
apply iff_trans with (1 := H1 s).
repeat rewrite in_map_iff; split; intros (x, (Hx1, Hx2)); exists x;
  try (rewrite H2); auto; rewrite <- H2; auto.
Qed.

Definition to6i3 l ll :=
  match l with (l1, l2, p) => to6i l2 ll l1 p end.

Definition to6a3 l ll :=
  match l with (l1, l2, p) => to6a l2 ll l1 p end.

Lemma make_listto6it3 c k ll :
  In k (to6it _ make_list ll c) ->
  In k ll \/ (valid3 (rev3 k) /\ to6i3 (rev3 k) c = true).
Proof.
intro F; case (make_listto6i _ _ _ F); auto.
intros (l3, (l4, (p, (Hp, (Hp1, (Hp2, (Hp3, Hp4))))))).
right; rewrite Hp; repeat split; auto.
Qed.

Lemma to6ai3 l ll :
  to6i3 l ll = false -> valid3 l -> to6i3 l (to6a3 l ll) = true.
Proof.
destruct l as ((l1,l2),p1); simpl.
intros H1 (H2, (H3, H4)).
apply to6ai; auto.
Qed.

Lemma to6aif3 l1 l2 ll :
  to6i3 l2 ll = false -> valid3 l1 -> valid3 l2 ->
  l1 <> l2 ->
  to6i3 l1 (to6a3 l2 ll) =  to6i3 l1 ll.
Proof.
destruct l2 as ((l3, l4), p2); simpl.
destruct l1 as ((l1, l2),p1); simpl.
intros H1 (H2, (H3, H4)) (H5, (H6, H7)) H8.
apply to6aif; auto.
case (list_eq_dec cube_dec l1 l3); auto; intros HH1.
case (list_eq_dec orientation_dec l2 l4); auto; intros HH2.
case (positive_dec p1 p2); auto; intros HH3.
case H8; rewrite HH1, HH2, HH3; auto.
Qed.

Lemma make_listto6ir3 c l ll :
  valid3 (rev3 l) -> to6i3 (rev3 l) c = true -> 
  In l  (to6it _ make_list ll c).
Proof.
destruct l as ((l1,l2),p1); simpl.
intros (H1, (H2, H3)) H5.
apply make_listto6ir; auto.
Qed.

Lemma states_equiv_to6a s ss ll :
  valid_state s ->
  (forall s : state, In s ss -> valid_state s) ->
  states_equiv ss ll -> to6i3 (encode_state s) ll = false ->
   states_equiv (s :: ss) (to6a3 (encode_state s) ll).
Proof.
intros H H1 H2 H3 l; split; intros H4.
- simpl.
  case (make_listto6it3 _ _ _ H4).
    now intros HH; inversion HH.
  intros (H5, H6).
  generalize H6; clear H6.
  case (list3_dec (rev3 l) (encode_state s)); intros H6.
    now rewrite <- H6, rev3_involutive; auto.
  rewrite to6aif3; auto.
    intros H7; right; unfold states_equiv in H2; rewrite <-H2.
    now apply make_listto6ir3; auto.
  apply encode_valid; auto.
- case (list3_dec (rev3 l) (encode_state s)); intros H6.
    apply make_listto6ir3; rewrite H6.
      now apply encode_valid; auto.
    now apply to6ai3; auto; apply encode_valid; auto.
  simpl in H4; case H4; clear H4; intros H4; auto.
    now case H6; rewrite <- H4, rev3_involutive; auto.
  unfold states_equiv in H2; rewrite <- H2 in H4.
  case (make_listto6it3 _ _ _ H4); auto.
    now intros HH; inversion HH.
  intros (H7, H8).
  apply make_listto6ir3; auto.
  rewrite to6aif3; auto.
  apply encode_valid; auto.
Qed.

Definition filter (s : to6 * to6) l := 
  let (states, nstates) := s in
  let ll := encode_state l in
  if to6i3 ll states then s else
  let states1 := to6a3 ll states in
  let nstates1 := to6a3 ll nstates in (states1, nstates1).

Lemma in_states_equiv ss ll s :
  valid_state s ->
  (forall s, In s ss -> valid_state s) ->
  states_equiv ss ll ->
  in_states s ss = to6i3 (encode_state s) ll.
Proof.
intros Hg Hg1 H.
assert (F0: valid3 (rev3 (rev3 (encode_state s)))).
  rewrite rev3_involutive.
  now apply encode_valid; auto.
generalize (in_states_correct s ss); case in_states;
  intros H1.
  assert (F1: In (rev3 (encode_state s)) (to6it _ make_list nil ll)).
    unfold states_equiv in H; rewrite H.
    change (rev3 (encode_state s)) with 
           ((fun x => rev3 (encode_state x)) s).
    now apply in_map; auto.
  case (make_listto6it3 _ _ _ F1).
    now intros HH; inversion HH.
  now rewrite rev3_involutive; auto; intros (HH1, HH2); auto.
generalize (make_listto6ir3 ll _ nil F0).
rewrite rev3_involutive; auto.
case (to6i3 (encode_state s) ll); auto.
unfold states_equiv in H; rewrite H.
intros H2; case H1.
generalize Hg1 H2; elim ss; simpl; auto; clear ss Hg1 H2 H H1.
intros s1 ss Hrec Hg1 Hg2.
case (Hg2 (refl_equal true)); intros HH.
  left.
  rewrite <- (encode_decode_state s1); auto.
  rewrite HH, encode_decode_state; auto.
right; apply Hrec; auto.
Qed.

Lemma filter_equiv ps ll s :
  valid_state s -> valid_pair ps -> incl (snd ps) (fst ps) ->
  pstates_equiv ps ll -> pstates_equiv (filters ps s) (filter ll s).
Proof.
destruct ps as (ss1, ss2).
destruct ll as (ll1, ll2); simpl.
intros Hg (Hg1, Hg2) Hi (H1, H2).
simpl in H1, H2.
unfold filter, filters, pstates_equiv.
rewrite in_states_equiv with (3 := H1); auto.
case_eq (to6i3 (encode_state s) ll1); simpl fst; simpl snd; auto.
split; apply states_equiv_to6a; auto.
generalize H.
rewrite  <- in_states_equiv with (3 := H1); auto.
rewrite  <- in_states_equiv with (3 := H2); auto.
intros HH.
generalize (in_states_correct s ss1); rewrite HH; intros HH1.
generalize (in_states_correct s ss2); case in_states; auto.
intros HH2; case HH1; auto with datatypes.
Qed.

Local Definition snextp s (x : list cube * list orientation * positive) :=
  match x with (l1, l2, p) => next s l1 l2 p end.

Lemma snext_equiv ps s ll l :
  valid_state s -> valid_pair ps -> incl (snd ps) (fst ps) ->
  pstates_equiv ps ll -> state_equiv s l ->
  pstates_equiv (nexts ps s) (snextp ll l).
Proof.
unfold nexts, snextp, next.
destruct ps as (ss1, ss2).
destruct ll as (ll1, ll2).
destruct l as ((l1,l2),p).
intros Hg Hg1 Hi H1 Hs.
simpl in Hg1, Hi, H1.
match goal with |- context[fold_left ?X _ _] =>
  change X with (fun ps f => filters ps (f s))
end.
match goal with |- context[fold_left ?X ?Y (ll1,?Z)] =>
  replace (fold_left X Y (ll1,Z)) with 
    (fold_left (fun ps f => filter ps (f (decode_state l1 l2 p))) Y (ll1,Z))
end.
  generalize ss1 ss2 s ll1 ll2 l1 l2 p Hg Hg1 Hi H1 Hs (movel_valid).
  clear  ss1 ss2 s ll1 ll2 l1 l2 p Hg Hg1 Hi H1 Hs.
  elim movel.
    now unfold pstates_equiv; simpl; auto.
  intros f lf Hrec ss1 ss2 s ll1 ll2 l1 l2 p Hg Hg1 Hi H1 Hs Hf.
  assert (F0: valid_state (f s)); auto with datatypes.
  repeat rewrite fold_left_cons.
  case_eq (filters (ss1, ss2) (f s)); intros ss3 ss4 Hss3.
  case_eq (filter (ll1, ll2) (f (decode_state l1 l2 p))); intros ll3 ll4 Hll3.
  generalize (filter_equiv _ _ _ F0 Hg1 Hi H1).
  rewrite Hss3.
  change (decode_state l1 l2 p) with (decode3 (l1, l2, p)) in Hll3.
  unfold state_equiv in Hs; rewrite Hs in Hll3; auto;
    rewrite encode_decode_state in Hll3; auto.
  rewrite Hll3; intros HH; case HH; auto; intros Hf1 Hf2.
  apply Hrec; auto with datatypes.
    now generalize (filters_valid (ss1, ss2) (f s));
        rewrite Hss3; intros HH1; case HH1; auto.
  now generalize (filters_incl (ss1, ss2) (f s));
      rewrite Hss3; auto.
generalize (ll1, ll2); elim movel; simpl; auto.
intros a l Hrec q; rewrite Hrec; auto.
unfold filter; case encode_state; auto.
intros (xx,yy); auto.
Qed.

Lemma fold_next_equiv ss1 ss2 ss ll1 ll2 ll :
  valid_pair (ss1, ss2) ->
  (forall s, In s ss -> valid_state s) ->
  incl ss ss1 ->
  pstates_equiv (ss1, ss2) (ll1, ll2) ->
  states_equiv ss ll ->
  pstates_equiv (fold_left nexts ss2 (ss1,ss))
    (to6it _ next (ll1,ll) ll2).
Proof.
intros (He1, He2) He3 H1 (H2, H3) H4.
simpl in He1, He2, H2, H3.
rewrite make_listto6fold. 
unfold pstates_equiv; unfold states_equiv in H3.
generalize ss1 ss2 ss ll1 ll He1 He2 He3 H1 H2 H3 H4.
elim (to6it _ make_list nil ll2);
    clear ss1 ss2 ss ll1 ll2 ll He1 He2 He3 H1 H2 H3 H4.
  intros ss1 ss2 ss ll1 ll He1 He2 He3 H1 H2; case ss2; auto.
  simpl; auto.
  intros s l HH; case (HH (rev3 (encode_state s))); intros _ HH1.
  now case HH1; simpl; auto with datatypes.
intros.
assert (F1: lequiv (map decode3 (a :: l)) ss2).
  intros s.
  split; intros H5.
    rewrite in_map_iff in H5; case H5; clear H5.
    intros l1 (Hl1, Hl2); subst.
    rewrite H3, in_map_iff in Hl2.
    case Hl2; intros s (Hs1, Hs2); subst.
    now rewrite  encode_decode_state; auto.
  rewrite <- (encode_decode_state s); auto.
  apply (in_map decode3).
  rewrite H3.
  now apply (in_map (fun x => (rev3 (encode_state x)))); auto.
rewrite fold_left_cons.
case_eq (snextp (ll1, ll) a); intros ll2 ll3 Hll2.
case_eq (nexts (ss1, ss) (decode3 a)); intros ss3 ss4 Hss3.
assert (Fga: valid_state (decode3 a)).
  assert (F3: In a (a :: l)); auto with datatypes.
  rewrite H3, in_map_iff in F3; case F3; intros s (Hs1, Hs2); subst a.
  now rewrite encode_decode_state; auto.
generalize (snext_equiv (ss1, ss) (decode3 a) (ll1, ll) a); auto.
rewrite Hss3; rewrite Hll2; intros HH; case HH; auto; clear HH;
   try (split; auto; fail).
  unfold state_equiv.
  assert (F3: In a (a :: l)); auto with datatypes.
  rewrite H3, in_map_iff in F3; case F3; intros s (Hs1, Hs2); subst a.
  now rewrite encode_decode_state; auto.
simpl; intros Heq1 Heq2.
case (H ss3 (map decode3 l) ss4 ll2 ll3); auto.
- generalize (nexts_valid (ss1, ss) (decode3 a)); auto.
  rewrite Hss3; intros HH; case HH; auto; clear HH.
  split; auto.
- intros s Hs.
  rewrite in_map_iff in Hs; case Hs; intros l1 (Hl1, Hl2); subst.
  assert (F3: In l1 (a :: l)); auto with datatypes.
  rewrite H3, in_map_iff in F3.
  case F3; intros s (Hs1, Hs2); subst.
  rewrite encode_decode_state; auto.
- generalize (nexts_valid (ss1, ss) (decode3 a)); auto.
  rewrite Hss3; intros HH; case HH; auto; clear HH.
  split; auto.
- generalize (nexts_incl (ss1,ss) (decode3 a));
    rewrite Hss3; auto.
- intros s; rewrite in_map_iff; split.
    intros Hs.
    assert (F2: In s (a :: l)); auto with datatypes.
    rewrite H3, in_map_iff in F2.
    case F2; intros s1 (Hs1, Hs2); subst.
    exists s1; split; auto.
    rewrite in_map_iff.
    exists (rev3 (encode_state s1)); split; auto.
    now rewrite <- encode_decode_state; auto.
  intros (s1, (Hs1, Hs2)); subst.
  rewrite in_map_iff in Hs2.
  case Hs2; intros l1 (Hl1, Hl2); subst.
  assert (F2: In l1 (a :: l)); auto with datatypes.
  rewrite H3, in_map_iff in F2.
  case F2; intros s1 (Hs3, Hs4); subst.
  rewrite (encode_decode_state s1); auto.
- intros F2 F3.
  case (fold_nexts_equiv (ss1, (map decode3 (a :: l)))
                (ss1, ss2) ss ss); simpl; auto.
  + split; simpl; auto.
    intros s; split; auto.
  + intros s; split; auto.
  + rewrite Hss3.
    intros Hf1 Hf2.
    split.
      rewrite <- Hll2 in F2.
      now apply states_equiv_equiv with (1 := F2); auto.
    rewrite <- Hll2 in F3.
    apply states_equiv_equiv with (1 := F3); auto.
Qed.

Lemma iter_aux_equiv n ps ll :
  valid_pair ps -> 
  pstates_equiv ps ll ->
  pstates_equiv (iters_aux n ps) (iter_aux n ll).
Proof.
revert ps ll; elim n; simpl; clear n; auto.
intros n Hrec (ss1, ss2) (ll1, ll2) Hg He.
case (fold_next_equiv ss1 ss2 nil ll1 ll2 OTO6); auto with datatypes.
- intros s HH; inversion HH.
- intros s HH; inversion HH.
- intros s; simpl; split; auto.
- case (fold_nexts_valid (ss1, ss2) nil); simpl; auto.
  intros s HH; inversion HH.
  match goal with |- context[fold_left ?X ?Y ?Z] =>
    set (u := fold_left X Y Z)
  end.
  match goal with |- context[fold_left ?X ?Y ?Z] =>
    change (fold_left X Y Z) with u; case u
   end.
  intros ss3 ss4.
  match goal with |- context[to6it _ ?X ?Y ?Z] =>
    case (to6it _ X Y Z)
  end.
  simpl; intros ll3 ll4 Hg3 Hg4 He3 He4.
  apply Hrec; auto; split; auto.
Qed.

Lemma iter_equiv n : pstates_equiv (iters n) (iter n).
Proof.
unfold iters, iter.
apply iter_aux_equiv; simpl; auto.
  now split; intros s [H | H]; try (case H; fail); subst; apply valid_state_init.
split; red; simpl fst; simpl snd.
  replace (to6it _ make_list nil s0) with
          (map (fun x => rev3 (encode_state x)) (init_state :: nil)).
    now intros s; split; auto.
  now apply refl_equal.
replace (to6it _ make_list nil s0) with
        (map (fun x => rev3 (encode_state x)) (init_state :: nil)).
  now intros s; split; auto.
apply refl_equal.
Qed.

Lemma iter_true_reachable n :
  (forall s, valid_state s -> to6i3 (encode_state s) (fst (iter n)) = true 
        -> nlreachable n s).
Proof.
generalize (iter_equiv n) (iters_correct n) (iters_valid n).
case (iters n); case (iter n); intros s1 s2 l1 l2; simpl.
intros (H1, _) (H2, _) (Hg1, Hg2) s Hg Hs.
rewrite <- H2.
rewrite <- (in_states_equiv l1 s1 s) in Hs; auto.
generalize (in_states_correct s l1); rewrite Hs; auto.
Qed.

Lemma iter_final n :
  let (s1,s2) := iter n in
   match s2 with 
    OTO6 => forall s, reachable s -> nlreachable (Nat.pred n) s
   | _  => True
   end.
Proof.
generalize (iter_equiv n) (iters_final n).
case (iters n); case (iter n).
intros s1 s2; case s2; auto.
intros l1 l2; case l2; auto.
intros s l3 [_ H1].
generalize (H1 (rev3 (encode_state s))).
simpl to6it; rewrite in_map_iff; intros [_ H2].
case H2; exists s; simpl; auto.
Qed.

Theorem reach11: forall s, reachable s -> nlreachable 11 s.
Proof.
native_cast_no_check (iter_final 12).
Time Qed.

(*****************************************************************************)
(*                                                                           *)
(*      Correction of the solver by equivalence                              *)
(*       with the naive model defined in BasicRubik                          *)
(*                                                                           *)
(*****************************************************************************)

Definition tstates_equiv pss pll := 
   states_equiv (fst (fst pss)) (fst (fst pll)) /\
   states_equiv (snd (fst pss)) (snd (fst pll)) /\
   states_equiv (snd pss) (snd pll).

Definition filter2 pmod (s : (to6 * to6) * to6) l := 
  let ll := encode_state l in
  let (ps, ns) := s in
  let (s1, s2) := ps in
    if (to6i3 ll s1 || to6i3 ll s2)%bool
    then s
    else match pmod with
         | xH => ((to6a3 ll s1,s2), to6a3 ll ns)
         | xO _ => ((s1, to6a3 ll s2), to6a3 ll ns)
         | xI _ => ((to6a3 ll s1, to6a3 ll s2), to6a3 ll ns)
         end. 

Lemma filter2_equiv p ps ll s :
  valid_state s -> valid_triple ps -> 
  (forall s1, In s1 (snd ps) -> In s1 (fst (fst ps)) \/ In s1 (snd (fst ps))) ->
  tstates_equiv ps ll -> tstates_equiv (filter2s p ps s) (filter2 p ll s).
Proof.
destruct ps as ((ss1, ss2), ss3).
destruct ll as ((ll1, ll2), ll3).
intros Hg ((Hg1, Hg2), Hg3) Hi (H1, (H2, H3)).
simpl in * |-.
unfold filter2, filter2s, tstates_equiv.
rewrite in_states_equiv with (3 := H1); auto.
case_eq (to6i3 (encode_state s) ll1); simpl fst; simpl snd; auto.
rewrite in_states_equiv with (3 := H2); auto.
case_eq (to6i3 (encode_state s) ll2); simpl fst; simpl snd; auto.
case p.
- intros _ H4 H5; split.
    now simpl; try apply states_equiv_to6a; auto.
  split.
    now simpl; try apply states_equiv_to6a; auto.
  simpl; try apply states_equiv_to6a; auto.
  generalize H4 H5.
  rewrite  <- in_states_equiv with (3 := H1); auto.
  rewrite  <- in_states_equiv with (3 := H2); auto.
  rewrite  <- in_states_equiv with (3 := H3); auto.
  intros H6 H7.
  generalize (in_states_correct s ss3); case in_states; auto.
  intros H8; case (Hi _ H8); auto; intros H9; contradict H9.
    now generalize (in_states_correct s ss1); rewrite H7; auto.
  generalize (in_states_correct s ss2); rewrite H6; auto.
- intros _ H4 H5; split.
  simpl; try apply states_equiv_to6a; auto.
  split.
    now simpl; try apply states_equiv_to6a; auto.
  simpl; try apply states_equiv_to6a; auto.
  generalize H4 H5.
  rewrite  <- in_states_equiv with (3 := H1); auto.
  rewrite  <- in_states_equiv with (3 := H2); auto.
  rewrite  <- in_states_equiv with (3 := H3); auto.
  intros H6 H7.
  generalize (in_states_correct s ss3); case in_states; auto.
  intros H8; case (Hi _ H8); auto; intros H9; contradict H9.
    now generalize (in_states_correct s ss1); rewrite H7; auto.
  generalize (in_states_correct s ss2); rewrite H6; auto.
- intros H4 H5; split.
    now simpl; try apply states_equiv_to6a; auto.
  split.
    now simpl; try apply states_equiv_to6a; auto.
  simpl; try apply states_equiv_to6a; auto.
  generalize H4 H5.
  rewrite  <- in_states_equiv with (3 := H1); auto.
  rewrite  <- in_states_equiv with (3 := H2); auto.
  rewrite  <- in_states_equiv with (3 := H3); auto.
  intros H6 H7.
  generalize (in_states_correct s ss3); case in_states; auto.
  intros H8; case (Hi _ H8); auto; intros H9; contradict H9.
  generalize (in_states_correct s ss1); rewrite H7; auto.
  generalize (in_states_correct s ss2); rewrite H6; auto.
Qed.

Definition next2 p ps l :=
Eval lazy beta delta [filter2] in
 let s := decode3 l in
 fold_left (fun ps f => let s1 := f s in filter2 p ps s1)
   movel ps.

Lemma next2_equiv p ps s ll l :
  valid_state s -> valid_triple ps -> 
  (forall s1, In s1 (snd ps) -> In s1 (fst (fst ps)) \/ In s1 (snd (fst ps))) ->
  tstates_equiv ps ll -> state_equiv s l ->
  tstates_equiv (next2s p ps s) (next2 p ll l).
Proof.
unfold next2s, next2.
destruct ps as (ss1, ss2).
destruct ll as (ll1, ll2).
intros Hg Hg1 Hi H1 Hs.
simpl in Hg1, Hi, H1.
match goal with |- context[fold_left ?X _ _] =>
  change X with (fun ps f => filter2s p ps (f s)) 
end.
match goal with |- context[fold_left ?X ?Y (ll1,?Z)] =>
  replace (fold_left X Y (ll1, Z))
  with (fold_left (fun ps f => filter2 p ps (f (decode3 l))) Y (ll1, Z))
end.
  generalize ss1 ss2 s ll1 ll2 l Hg Hg1 Hi H1 Hs (movel_valid).
  clear  ss1 ss2 s ll1 ll2 l Hg Hg1 Hi H1 Hs.
  elim movel.
    now unfold tstates_equiv; simpl; auto.
  intros f lf Hrec ss1 ss2 s ll1 ll2 l Hg Hg1 Hi H1 Hs Hf.
  assert (F0: valid_state (f s)); auto with datatypes.
  repeat rewrite fold_left_cons.
  case_eq (filter2s p (ss1, ss2) (f s)); intros ss3 ss4 Hss3.
  case_eq (filter2 p (ll1, ll2) (f (decode3 l))); intros ll3 ll4 Hll3.
  generalize (filter2_equiv p _ _ _ F0 Hg1 Hi H1).
  rewrite Hss3.
  unfold state_equiv in Hs; rewrite Hs, encode_decode_state in Hll3; auto.
  rewrite Hll3; intros HH; case HH; auto; intros Hf1 (Hf2, Hf3).
  simpl in Hf1, Hf2, Hf3.
  apply Hrec; auto with datatypes.
    now generalize (filter2s_valid p (ss1, ss2) (f s));
        rewrite Hss3; intros HH1; case HH1; auto.
  now generalize (filter2s_incl p (ss1, ss2) (f s));
      rewrite Hss3; auto.
generalize (ll1, ll2); elim movel; simpl; auto.
Qed.

Definition next2p p c l1 l2 p1 := next2 p c (l1,l2, p1).

Lemma fold_next2_equiv p ss1 ss2 ss ll1 ll2 ll :
  valid_triple (ss1, ss2) ->
  (forall s, In s ss -> valid_state s) ->
  (forall s1, In s1 ss -> In s1 (fst ss1) \/ In s1 (snd ss1)) ->
  tstates_equiv (ss1, ss2) (ll1, ll2) ->
  states_equiv ss ll ->
  tstates_equiv (fold_left (next2s p) ss2 (ss1,ss))
    (to6it _ (next2p p) (ll1,ll) ll2).
Proof.
intros ((He1, He2), He3) He4 H1 (H2, (H3, H4)) H5.
simpl in He1, He2, He3, H2, H3, H4.
rewrite make_listto6fold. 
unfold tstates_equiv; unfold states_equiv in H4.
generalize ss1 ss2 ss ll1 ll He1 He2 He3 He4 H1 H2 H3 H4 H5.
elim (to6it _ make_list nil ll2);
    clear ss1 ss2 ss ll1 ll2 ll He1 He2 He3 He4 H1 H2 H3 H4 H5.
  intros ss1 ss2 ss ll1 ll He1 He2 He3 H4 H1 H2 H3; case ss2; auto.
  simpl; auto.
  intros s l HH; case (HH (rev3 (encode_state s))); intros _ HH1.
  now case HH1; simpl; auto with datatypes.
intros.
assert (F1: lequiv (map decode3 (a :: l)) ss2).
  intros s.
  split; intros H6.
    rewrite in_map_iff in H6; case H6; clear H6.
    intros l1 (Hl1, Hl2); subst.
    rewrite H4, in_map_iff in Hl2.
    case Hl2; intros s (Hs1, Hs2); subst.
    now rewrite encode_decode_state; auto.
  rewrite <- (encode_decode_state s); auto.
  apply (in_map decode3).
  rewrite H4.
  now apply (in_map (fun x => (rev3 (encode_state x)))); auto.
rewrite fold_left_cons.
case_eq (next2 p (ll1, ll) a); intros ll2 ll3 Hll2.
case_eq (next2s p (ss1, ss) (decode3 a)); intros ss3 ss4 Hss3.
assert (Fga: valid_state (decode3 a)).
  assert (F3: In a (a :: l)); auto with datatypes.
  rewrite H4, in_map_iff in F3; case F3; intros s (Hs1, Hs2); subst a.
  now rewrite encode_decode_state; auto.
generalize (next2_equiv p (ss1, ss) (decode3 a) (ll1, ll) a); auto.
rewrite Hss3; rewrite Hll2; intros HH; case HH; auto; clear HH;
    try (split; auto; fail).
  unfold state_equiv.
  assert (F3: In a (a :: l)); auto with datatypes.
  rewrite H4, in_map_iff in F3; case F3; intros s (Hs1, Hs2); subst a.
  now rewrite encode_decode_state; auto.
simpl; intros Heq1 (Heq2, Heq3).
case (H ss3 (map decode3 l) ss4 ll2 ll3); auto.
- generalize (next2s_valid p  (ss1, ss) (decode3 a)); auto.
  rewrite Hss3; intros HH; case HH; auto; clear HH.
    now split; auto.
  intros HH; case HH; auto.
- generalize (next2s_valid p  (ss1, ss) (decode3 a)); auto.
  rewrite Hss3; intros HH; case HH; auto; clear HH.
    now split; auto.
  intros HH; case HH; auto.
- intros s Hs.
  rewrite in_map_iff in Hs; case Hs; intros l1 (Hl1, Hl2); subst.
  assert (F3: In l1 (a :: l)); auto with datatypes.
  rewrite H4, in_map_iff in F3.
  case F3; intros s (Hs1, Hs2); subst.
  rewrite encode_decode_state; auto.
- generalize (next2s_valid p (ss1, ss) (decode3 a)); auto.
  rewrite Hss3; intros HH; case HH; auto; clear HH.
  now split; auto.
- generalize (next2s_incl p (ss1,ss) (decode3 a));
  rewrite Hss3; auto.
- intros s; rewrite in_map_iff; split.
    intros Hs.
    assert (F2: In s (a :: l)); auto with datatypes.
    rewrite H4, in_map_iff in F2.
    case F2; intros s1 (Hs1, Hs2); subst.
    exists s1; split; auto.
    rewrite in_map_iff.
    exists (rev3 (encode_state s1)); split; auto.
    now rewrite <- encode_decode_state; auto.
  intros (s1, (Hs1, Hs2)); subst.
  rewrite in_map_iff in Hs2.
  case Hs2; intros l1 (Hl1, Hl2); subst.
  assert (F2: In l1 (a :: l)); auto with datatypes.
  rewrite H4, in_map_iff in F2.
  case F2; intros s1 (Hs3, Hs4); subst.
  rewrite (encode_decode_state s1); auto.
- intros F2 (F3, F4).
  case (fold_next2s_equiv p (ss1, (map decode3 (a :: l)))
                (ss1, ss2) ss ss); simpl; auto.
  + split; simpl; auto.
      now intros s; split; auto.
    split; auto.
    intros s; split; auto.
  + intros s; split; auto.
  + unfold BasicRubik.states in Hss3 |- *; rewrite Hss3.
    intros H6 (H7, H8).
    split.
      generalize F2; rewrite <- Hll2; case a; clear F2.
      intros (lc,lo) p1 F2.
      now apply states_equiv_equiv with (1 := F2); auto.
(* apply states_equiv_equiv with (1 := F4); auto. *)
    split.
      generalize F3; rewrite <- Hll2; case a; clear F3.
      intros (lc,lo) p1 F3.
      now apply states_equiv_equiv with (1 := F3); auto.
    generalize F4; rewrite <- Hll2; case a; clear F4.
    intros (lc,lo) p1 F4.
    apply states_equiv_equiv with (1 := F4); auto.
Qed.

Fixpoint iter2_aux n p (ps: (to6 * to6) * to6) := 
  match n with 
   O => ps 
 | S n1 => let (m,p1) := ps in 
           iter2_aux n1 (pos_up p) (to6it _ (next2p p) (m, OTO6) p1)
  end.

Lemma iter2_aux_equiv n p ps ll :
  valid_triple ps -> 
  tstates_equiv ps ll ->
  tstates_equiv (iter2s_aux n p ps) (iter2_aux n p ll).
Proof.
revert p ps ll.
elim n; simpl; clear n; auto.
intros n Hrec p (ss1, ss2) (ll1, ll2) Hg He.
case (fold_next2_equiv p ss1 ss2 nil ll1 ll2 OTO6); auto with datatypes.
  now intros s HH; inversion HH.
  now intros s HH; inversion HH.
  now intros s; simpl; split; auto.
case (fold_next2s_valid p (ss1, ss2) nil); simpl; auto.
  now intros s HH; inversion HH.
match goal with |- context[fold_left ?X ?Y ?Z] =>
  case (fold_left X Y Z)
end.
intros ss3 ss4.
match goal with |- context[to6it _ ?X ?Y ?Z] =>
  case (to6it _ X Y Z)
end.
simpl; intros ll3 ll4 Hg3 Hg4 He3 He4.
apply Hrec; auto; split; auto.
Qed.

Definition iter2 n := iter2_aux n 2%positive (s0, OTO6, s0).

Lemma iter2_equiv n : tstates_equiv (iter2s n) (iter2 n).
Proof.
unfold iter2s, iter2.
assert (F: to6it _ make_list nil s0 =
        (map (fun x => rev3 (encode_state x)) (init_state :: nil))).
  now apply refl_equal.
apply iter2_aux_equiv; simpl; auto.
  split; [split | idtac].
    now intros s [H | H]; try (case H; fail); subst; apply valid_state_init.
    now intros s HH; case HH.
  now intros s [H | H]; try (case H; fail); subst; apply valid_state_init.
split; [split | idtac]; simpl fst; try rewrite F; auto.
split; simpl.
  now intros s; split; auto.
unfold states_equiv.
intros s; rewrite F.
split; auto.
Qed.

Lemma iter2_final n :
  let (ps,s3) := iter2 n in
  let (s1,s2) := ps in
   match s3 with 
    OTO6 =>
  (forall s, reachable s -> to6i3 (encode_state s) s1 = true \/ 
                            to6i3 (encode_state s)  s2 = true) /\
  (forall s, valid_state s -> to6i3 (encode_state s) s1 = true -> 
     exists m1, (m1 <= n)%nat /\ nsreachable m1 s /\ is_odd (porder m1)) /\
  (forall s, valid_state s -> to6i3 (encode_state s) s2 = true ->
     exists m1, (m1 <= n)%nat /\ nsreachable m1 s /\ porder m1 <> 1%positive)
   | _  => True
   end.
Proof.
generalize (iter2_equiv n) (iter2s_final n) (iter2s_valid n).
case (iter2s n); case (iter2 n).
intros (s1, s2) s3; case s3; auto.
intros (l1, l2) l3; case l3; auto.
  intros (H1, (H2, _)); simpl in H1, H2.
  intros (H3, (H4, H5)) ((Hg1, Hg2),_); simpl in Hg1, Hg2.
  split; [idtac | split].
    intros s Hs; case (H3 _ Hs); intros Hs1.
      assert (F1: In (rev3 (encode_state s)) (map (fun x : state => rev3 (encode_state x)) l1)).
        now rewrite in_map_iff; exists s; auto.
      rewrite <- (H1 (rev3 (encode_state s))) in F1.
      case (make_listto6it3 _ _ _ F1); auto.
      rewrite rev3_involutive; auto.
      now intros (HH1, HH2); auto.
    assert (F1: In (rev3 (encode_state s)) (map (fun x : state => rev3 (encode_state x)) l2)).
      now rewrite in_map_iff; exists s; auto.
    rewrite <- (H2 (rev3 (encode_state s))) in F1.
    case (make_listto6it3 _ _ _ F1); auto.
    rewrite rev3_involutive; auto.
    now intros (HH1, HH2); auto.
  intros s Hg Hs.
    assert (F1:= encode_valid _ Hg).
    rewrite <- (rev3_involutive (encode_state s)) in Hs, F1.
    generalize (make_listto6ir3 _ _ nil F1 Hs).
    rewrite (H1 (rev3 (encode_state s))), in_map_iff.
    intros (s', (Hs', Hs1')).
    assert (s' = s); subst; auto.
    rewrite <- (encode_decode_state s'); auto.
    now rewrite Hs', encode_decode_state; auto.
  intros s Hg Hs.
  assert (F1:= encode_valid _ Hg).
  rewrite <- (rev3_involutive (encode_state s)) in Hs, F1.
  generalize (make_listto6ir3 _ _ nil F1 Hs).
  rewrite (H2 (rev3 (encode_state s))), in_map_iff.
  intros (s', (Hs', Hs1')).
  assert (s' = s); subst; auto.
  rewrite <- (encode_decode_state s'); auto.
  now rewrite Hs', encode_decode_state; auto.
intros s l (H1, (H2, H3)) _ ((Hg1, Hg2), _); simpl in H1, H2, H3, Hg1, Hg2.
generalize (H3 (rev3 (encode_state s))).
simpl to6it; rewrite in_map_iff; intros [_ HH].
case HH; exists s; simpl; auto.
Qed.

(* A transcription of to6 of the solver *)
Definition to6_get_number s s1 s2 :=
  let l := encode_state s in
  if to6i3 l s1 then
    if to6i3 l s2 then 3%positive else 1%positive
  else
    if to6i3 l s2 then 2%positive else 4%positive.

Fixpoint to6_get_next_aux n s s1 s2 l :=
  match l with
  | nil => None
  | a :: l1 => if positive_eq n (to6_get_number (m2f a s) s1 s2) then Some a
             else to6_get_next_aux n s s1 s2 l1
  end.

Definition to6_get_next s s1 s2 := to6_get_next_aux (pos_down (to6_get_number s s1 s2)) s s1 s2 Movel.


Definition to6_step f s s1 s2 :=
    match to6_get_next s s1 s2 return list moves with
             None => nil
            | Some a => a ::  f (m2f a s) s1 s2 
            end.

Fixpoint to6_solve n s s1 s2 :=
  match n with
   O => nil
  | S n1 => to6_step (to6_solve n1) s s1 s2 
  end.

Lemma to6_get_number_equiv s s1 s2 l1 l2 :
  valid_state s -> valid_pair (s1, s2) ->
  pstates_equiv (s1,s2) (l1,l2) ->
    get_number s s1 s2 = to6_get_number s l1 l2.
Proof.
intros Hg (Hg1, Hg2) (H1, H2); simpl in Hg1, Hg2, H1, H2.
unfold get_number, to6_get_number.
rewrite (in_states_equiv s1 l1); auto.
rewrite (in_states_equiv s2 l2); auto.
Qed.

Lemma to6_get_next_aux_equiv n s s1 s2 l1 l2 l :
  valid_state s -> valid_pair (s1, s2) ->
  pstates_equiv (s1,s2) (l1,l2) -> incl l Movel  ->
    get_next_aux n s s1 s2 l = to6_get_next_aux n s l1 l2 l.
Proof.
intros Hg (Hg1, Hg2) (H1, H2); 
  elim l; simpl; auto; clear l.
intros a l Hrec Hi; rewrite Hrec; auto with datatypes.
  rewrite  <- (fun x => to6_get_number_equiv x s1 s2); auto.
    apply move_valid with s; auto.
    now apply Movel_move; auto with datatypes.
    now split; auto.
  now split; auto.
apply incl_tran with (2 := Hi); auto with datatypes.
Qed.

Lemma to6_get_next_movel s l1 l2 :
    match to6_get_next s l1 l2 with
      Some m => In m Movel | _ => True
    end.
Proof.
unfold to6_get_next.
elim Movel; simpl; auto.
intros a l Hrec; case positive_eq; auto.
generalize Hrec; case to6_get_next_aux; auto with datatypes.
Qed.

Lemma to6_get_next_equiv s s1 s2 l1 l2 :
  valid_state s -> valid_pair (s1, s2) ->
  pstates_equiv (s1,s2) (l1,l2) -> 
    get_next s s1 s2 = to6_get_next s l1 l2.
Proof.
intros Hg Hg1 H1.
unfold to6_get_next, get_next.
rewrite (to6_get_number_equiv _ _ _ _ _ Hg Hg1 H1).
apply to6_get_next_aux_equiv; auto with datatypes.
Qed.

Lemma to6_solve_equiv n s s1 s2 l1 l2 :
  valid_state s -> valid_pair (s1, s2) ->
  pstates_equiv (s1,s2) (l1,l2) -> 
    solve n s s1 s2 = to6_solve n s l1 l2.
Proof.
intros Hs Hg H1; generalize s Hs; elim n; simpl; 
  auto; clear n s Hs.
intros n Hrec s Hs; unfold to6_step.
rewrite (to6_get_next_equiv s s1 s2 l1 l2); auto.
generalize (to6_get_next_movel s l1 l2); case to6_get_next; auto.
intros m Hm; rewrite Hrec; auto.
apply move_valid with s; auto.
apply Movel_move; auto with datatypes.
Qed.

Lemma to6_solve_init n s s1 s2 :
  (s1, s2) = fst (iter2 n) ->
  nlreachable n s -> 
  fold_left (fun s a => m2f a s) (to6_solve n s s1 s2) s = init_state.
Proof.
intros H1 H2.
rewrite <- (to6_solve_equiv n s (fst (fst (iter2s n))) (snd (fst (iter2s n))) s1 s2).
- apply solve_init; auto.
  case (fst (iter2s n)); auto.
- case (nlreachable_bound _ _ H2); clear H2; intros m (H2, H3).
  apply nreachable_valid with m; case H3; auto.
- generalize (iter2s_valid n).
  intros (HH1, HH2); auto.
- rewrite H1; case (iter2_equiv n); intros HH (HH1, _); split; auto.
Qed.

Lemma to6_solve_length n s s1 s2 :
  (s1, s2) = fst (iter2 n) ->
  valid_state s -> 
  (length (to6_solve n s s1 s2) <= n)%nat.
Proof.
intros H1 H.
rewrite <- (to6_solve_equiv n s (fst (fst (iter2s n))) (snd (fst (iter2s n))) s1 s2); auto.
- apply solve_length; auto.
- generalize (iter2s_valid n).
  intros (HH1, HH2); auto.
- rewrite H1; case (iter2_equiv n); intros HH (HH1, _); split; auto.
Qed.