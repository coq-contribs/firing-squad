(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V6.3                                  *)
(*                               Dec 24 1996                                *)
(*                                                                          *)
(****************************************************************************)
(*              Firing Squad Synchronization Problem                        *)
(*                                                                          *)
(*              Jean Duprat                                                 *)
(*                                                                          *)
(*              Developped in V5.10  July 1997                              *)
(****************************************************************************)

Require Export Arith.
Require Export Peano_dec.
Require Export Compare_dec.

Global Set Asymmetric Patterns.

Section bibliotheque.

Section regles.

Definition ifdec (A B : Prop) (C : Set) (H : {A} + {B}) 
  (x y : C) : C := match H return C with
                   | left _ => x
                   | right _ => y
                   end.

Notation Ifdec := (ifdec _ _ _) (only parsing).

Theorem Ifdec_left :
 forall (A B : Prop) (C : Set) (H : {A} + {B}) (x y : C),
 ~ B -> ifdec _ _ _ H x y = x.
intros; case H; trivial with v62.
intro; absurd B; trivial with v62.
Qed.

Theorem Ifdec_right :
 forall (A B : Prop) (C : Set) (H : {A} + {B}) (x y : C),
 ~ A -> ifdec _ _ _ H x y = y.
intros; case H; trivial with v62.
intro; absurd A; trivial with v62.
Qed.

Lemma and_impl : forall A B : Prop, A -> (A -> B) -> A /\ B.
intuition.
Qed.

Lemma recur_nSn :
 forall (P : nat -> Prop) (n : nat),
 P n ->
 P (S n) ->
 (forall p : nat, P p -> P (S p) -> P (S (S p))) ->
 forall p : nat, n <= p -> P p.
intros; cut (P p /\ P (S p)); intros.
elim H3; auto with v62.

elim H2; split; auto with v62.
elim H4; auto with v62.

apply H1; elim H4; auto with v62.
Qed.

Lemma recur2 :
 forall P : nat -> Prop,
 (forall n : nat, (forall p : nat, p < n -> P p) -> P n) ->
 forall m : nat, P m.
intros; apply H; elim m.
intros; absurd (p < 0); auto with v62.

intros; case (le_lt_eq_dec p n) as [ | -> ]; auto with v62.
Qed.

Theorem Rec2 : forall A B C : Prop, (A -> B -> C) -> A -> (A -> B) -> C.
intuition.
Qed.

Theorem Rec3 :
 forall A B C D : Prop, (A -> B -> C -> D) -> A -> B -> (B -> C) -> D.
intuition.
Qed.

Theorem Rec3' :
 forall A B C D : Prop,
 (A -> B -> C -> D) -> A -> (A -> B) -> (A -> B -> C) -> D.
intuition.
Qed.

Theorem Rec4 :
 forall A B C D E : Prop,
 (A -> B -> C -> D -> E) -> A -> B -> (B -> C) -> (C -> D) -> E.
intuition.
Qed.

Theorem Rec4' :
 forall A B C D E : Prop,
 (A -> B -> C -> D -> E) -> A -> B -> C -> (B -> C -> D) -> E.
intuition.
Qed.

Theorem Rec4'' :
 forall A B C D E : Prop,
 (A -> B -> C -> D -> E) -> A -> (A -> B) -> (B -> C) -> (C -> D) -> E.
intuition.
Qed.

Theorem Rec5 :
 forall A B C D E F : Prop,
 (A -> B -> C -> D -> E -> F) ->
 A -> B -> (B -> C) -> (C -> D) -> (D -> E) -> F.
intuition.
Qed.

Theorem Rec5' :
 forall A B C D E F : Prop,
 (A -> B -> C -> D -> E -> F) ->
 A -> B -> (A -> C) -> (B -> C -> D) -> (C -> D -> E) -> F.
intuition.
Qed.

End regles.

Section arithmetique.

Lemma plus_S : forall n m : nat, S n + m = S (n + m).
auto with v62.
Qed.

Lemma S_pred : forall x : nat, 0 < x -> x = S (pred x).
intros; case H; intros; simpl; auto with v62.
Qed.

Lemma plus_pred : forall n m : nat, 0 < n -> pred n + m = pred (n + m).
intros; apply eq_add_S.
rewrite <- S_pred.
rewrite <- plus_S; rewrite <- S_pred; auto with v62.

apply lt_plus_trans; auto with v62.
Qed.

Lemma SS_pred : forall x : nat, 1 < x -> x = S (S (pred (pred x))).
intros; case H; intros; simpl; auto with v62.
apply eq_S; rewrite <- S_pred; auto with v62.
Qed.

Lemma Sminus_aSb : forall a b : nat, b < a -> S (a - S b) = a - b.
intros; rewrite minus_Sn_m; auto with v62.
Qed.

Lemma lt_plus_plus : forall n m p q : nat, n < m -> p < q -> n + p < m + q.
intros; apply lt_trans with (m := n + q).
apply plus_lt_compat_l; auto with v62.

apply plus_lt_compat_r; auto with v62.
Qed.

Lemma lt_not_eq : forall n m : nat, n < m -> n <> m.
intros; red; intros.
rewrite H0 in H; absurd (m < m); auto with v62.
Qed.

End arithmetique.

Section naturels.

Definition un := 1.
Definition deux := 2.
Definition trois := 3.
Definition quatre := 4.
Definition cinq := 5.
Definition six := 6.
Definition sept := 7.
Definition huit := 8.
Definition neuf := 9.

Lemma plus_zero : forall n : nat, n + 0 = n.
intros; rewrite <- plus_n_O; auto with v62.
Qed.

Lemma plus_un : forall n : nat, n + un = S n.
intros; unfold un; rewrite <- plus_n_Sm; auto with v62.
Qed.

Lemma minus_un : forall n : nat, n - un = pred n.
intros; case n; simpl; auto with v62.
Qed.

Lemma Sminus_un : forall n : nat, un <= n -> S (n - un) = n.
intros; rewrite minus_un; rewrite <- S_pred; auto with v62.
Qed.

Lemma plus_deux : forall n : nat, n + deux = S (S n).
intros; unfold deux; repeat rewrite <- plus_n_Sm; auto with v62.
Qed.

Lemma minus_deux : forall n : nat, n - deux = pred (pred n).
intros; case n; simpl; auto with v62.
intros; apply minus_un; auto with v62.
Qed.

Lemma SSminus_deux : forall n : nat, deux <= n -> S (S (n - deux)) = n.
intros; rewrite minus_deux; do 2 (rewrite <- S_pred; auto with v62).
Qed.

Lemma plus_trois : forall n : nat, n + trois = S (S (S n)).
intros; unfold trois; repeat rewrite <- plus_n_Sm; auto with v62.
Qed.

Lemma minus_trois : forall n : nat, n - trois = pred (pred (pred n)).
intros; case n; simpl; auto with v62.
intros; apply minus_deux; auto with v62.
Qed.

Lemma SSSminus_trois :
 forall n : nat, trois <= n -> S (S (S (n - trois))) = n.
intros; unfold trois; rewrite Sminus_aSb; auto with v62.
rewrite SSminus_deux; auto with v62.
Qed.

Lemma plus_quatre : forall n : nat, n + quatre = S (S (S (S n))).
intros; unfold quatre; repeat rewrite <- plus_n_Sm; auto with v62.
Qed.

Lemma plus_cinq : forall n : nat, n + cinq = S (S (S (S (S n)))).
intros; unfold cinq; rewrite <- plus_n_Sm; rewrite plus_quatre;
 auto with v62.
Qed.

Lemma plus_six : forall n : nat, n + six = S (S (S (S (S (S n))))).
intros; unfold six; repeat rewrite <- plus_n_Sm; rewrite plus_zero;
 auto with v62.
Qed.

Lemma plus_sept : forall n : nat, n + sept = S (S (S (S (S (S (S n)))))).
intros; unfold sept; repeat rewrite <- plus_n_Sm; rewrite plus_zero;
 auto with v62.
Qed.

Lemma plus_huit : forall n : nat, n + huit = S (S (S (S (S (S (S (S n))))))).
intros; unfold huit; repeat rewrite <- plus_n_Sm; rewrite plus_zero;
 auto with v62.
Qed.

Lemma plus_neuf :
 forall n : nat, n + neuf = S (S (S (S (S (S (S (S (S n)))))))).
intros; unfold neuf; repeat rewrite <- plus_n_Sm; rewrite plus_zero;
 auto with v62.
Qed.

Lemma lt_deux_O : forall n : nat, deux < n -> 0 < n.
intros; apply lt_trans with (m := un); auto with v62.
Qed.

Lemma le6_lt2 : forall n : nat, six <= n -> deux < n.
intros; apply lt_le_trans with (m := 6); auto with v62.
Qed.

Lemma lt_O_minus : forall n m : nat, m < n -> 0 < n - m.
intros; apply plus_lt_reg_l with (p := m).
rewrite plus_zero; rewrite le_plus_minus_r; auto with v62.
Qed.

End naturels.

Section double_triple.

Definition double (p : nat) := p + p.

Lemma lt_O_double : forall n : nat, 0 < n -> 0 < double n.
intros; unfold double; apply lt_plus_trans; auto with v62.
Qed.

Lemma double_S : forall n : nat, double (S n) = S (S (double n)).
unfold double; intros.
rewrite <- plus_n_Sm; simpl; auto with v62.
Qed.

Lemma le_double : forall n m : nat, double n <= double m -> n <= m.
intros n m; case (le_lt_dec n m); intros; auto with v62.
absurd (double n <= double m); auto with v62.
apply lt_not_le.
unfold double; apply lt_trans with (m := n + m).
apply plus_lt_compat_r; auto with v62.

apply plus_lt_compat_l; auto with v62.
Qed.

Lemma le_S_double : forall n m : nat, double n <= S (double m) -> n <= m.
intros n m; case (le_lt_dec n m); intros; auto with v62.
absurd (double n <= S (double m)); auto with v62.
apply lt_not_le.
unfold double; apply le_lt_trans with (m := n + m).
apply lt_le_S; apply plus_lt_compat_r; auto with v62.

apply plus_lt_compat_l; auto with v62.
Qed.

Definition triple (p : nat) := p + p + p.

Lemma le_triple : forall n m : nat, triple n <= triple m -> n <= m.
intros n m; case (le_lt_dec n m); intros; auto with v62.
absurd (triple m < triple n); auto with v62.
unfold triple; repeat (apply lt_plus_plus; auto with v62).
Qed.

Lemma lt_triple : forall n m : nat, triple n < triple m -> n < m.
intros n m; case (le_lt_dec m n); intros; auto with v62.
absurd (triple m <= triple n); auto with v62.
unfold triple; repeat (apply plus_le_compat; auto with v62).
Qed.

Lemma triple_S : forall n : nat, triple (S n) = S (S (S (triple n))).
intros; unfold triple; repeat rewrite <- plus_n_Sm; auto with v62.
Qed.

Lemma le_n_triplem : forall n m : nat, n <= m -> n <= triple m.
intros; unfold triple; do 2 apply le_plus_trans; auto with v62.
Qed.

Lemma le_SSS_triple : forall n : nat, deux <= n -> S (S (S n)) <= triple n.
intros; rewrite <- (plus_trois n); rewrite plus_comm; unfold triple;
 apply plus_le_compat_r.
apply le_trans with (m := deux + deux); auto with v62.
apply plus_le_compat; auto with v62.
Qed.

Lemma le_double_triple : forall n : nat, double n <= triple n.
intro; unfold double, triple; apply le_plus_l.
Qed.

End double_triple.

Section modulo_2.

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n : nat, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n : nat, even n -> odd (S n).

Inductive div2 (a : nat) : Set :=
  | reste_2_0 : forall q : nat, even a -> a = double q -> div2 a
  | reste_2_1 : forall q : nat, odd a -> a = S (double q) -> div2 a.

Theorem quotient2 : forall a : nat, div2 a.
simple induction a.
apply reste_2_0 with (q := 0); auto with v62.
apply even_O.

clear a; intros.
elim H; intros.
apply reste_2_1 with (q := q); auto with v62.
apply odd_S; auto with v62.

apply reste_2_0 with (q := S q).
apply even_S; auto with v62.

rewrite double_S; auto with v62.
Defined.

End modulo_2.

Section modulo_3.

Inductive div3 (a : nat) : Set :=
  | reste_3_0 : forall q : nat, a = triple q -> div3 a
  | reste_3_1 : forall q : nat, a = S (triple q) -> div3 a
  | reste_3_2 : forall q : nat, a = S (S (triple q)) -> div3 a.

Theorem quotient3 : forall n : nat, div3 n.
simple induction n.
apply reste_3_0 with (q := 0); auto with v62.

clear n; intros; elim H; intros.
apply reste_3_1 with (q := q); auto with v62.

apply reste_3_2 with (q := q); auto with v62.

apply reste_3_0 with (q := S q); auto with v62.
rewrite triple_S; rewrite e; auto with v62.
Defined.

Definition tiers (n : nat) :=
  match quotient3 n return nat with
  | reste_3_0 q _ => q
  | reste_3_1 q _ => q
  | reste_3_2 q _ => q
  end.

Definition reste3 (n : nat) :=
  match quotient3 n return nat with
  | reste_3_0 q _ => 0
  | reste_3_1 q _ => 1
  | reste_3_2 q _ => 2
  end.

Definition Omod3 (n : nat) := reste3 n = 0.

Definition Unmod3 (n : nat) := reste3 n = 1.

Definition Deuxmod3 (n : nat) := reste3 n = 2.

Lemma le_tiers_Stiers : forall n : nat, tiers n <= tiers (S n).
intros; unfold tiers; simpl; case (quotient3 n);
 simpl; intros; auto with v62.
Qed.

Lemma triple_tiers :
 forall n : nat, Omod3 n -> tiers n + tiers n + tiers n = n.
intros n; unfold Omod3, reste3, tiers; case (quotient3 n);
 auto with v62.
intros; absurd (1 = 0); auto with v62.

intros; absurd (2 = 0); auto with v62.
Qed.

Lemma Striple_tiers :
 forall n : nat, Unmod3 n -> S (tiers n + tiers n + tiers n) = n.
intros n; unfold Unmod3, reste3, tiers; case (quotient3 n);
 auto with v62.
intros; absurd (0 = 1); auto with v62.

intros; absurd (2 = 1); auto with v62.
Qed.

Lemma SStriple_tiers :
 forall n : nat, Deuxmod3 n -> S (S (tiers n + tiers n + tiers n)) = n.
intros n; unfold Deuxmod3, reste3, tiers; case (quotient3 n);
 auto with v62.
intros; absurd (0 = 2); auto with v62.

intros; absurd (1 = 2); auto with v62.
Qed.

Lemma plus_deuxtiers_untiers :
 forall n : nat, Omod3 n -> double (tiers n) + tiers n = n.
intros; unfold double; apply triple_tiers; auto with v62.
Qed.

Lemma Splus_deuxtiers_untiers :
 forall n : nat, Unmod3 n -> S (double (tiers n) + tiers n) = n.
intros; unfold double; apply Striple_tiers; auto with v62.
Qed.

Lemma SSplus_deuxtiers_untiers :
 forall n : nat, Deuxmod3 n -> S (S (double (tiers n) + tiers n)) = n.
intros; unfold double; apply SStriple_tiers; auto with v62.
Qed.

Lemma lt_tiersn_n : forall n : nat, 0 < n -> tiers n < n.
intros n; unfold tiers; case (quotient3 n); intros q He; rewrite He.
case q; unfold triple.
simpl; intros; absurd (0 < 0); auto with v62.

intros; apply lt_plus_trans; pattern (S n0) at 1;
 rewrite <- (plus_zero (S n0)).
apply plus_lt_compat_l; auto with v62.

intros; pattern q at 1; rewrite <- (plus_zero q);
 unfold triple.
rewrite plus_assoc_reverse; rewrite plus_n_Sm; apply plus_lt_compat_l;
 auto with v62.

intros; pattern q at 1; rewrite <- (plus_zero q);
 unfold triple.
rewrite plus_assoc_reverse; do 2 rewrite plus_n_Sm; apply plus_lt_compat_l;
 auto with v62.
Qed.

Lemma lt_deuxtiersn_n : forall n : nat, 0 < n -> double (tiers n) < n.
intros n; unfold tiers; case (quotient3 n); intros q He; rewrite He.
case q; unfold double, triple.
simpl; intros; absurd (0 < 0); auto with v62.

intros; pattern (S n0 + S n0) at 1;
 rewrite <- (plus_zero (S n0 + S n0)); apply plus_lt_compat_l; 
 auto with v62.

intros; unfold double, triple; pattern (q + q) at 1;
 rewrite <- (plus_zero (q + q)); rewrite plus_n_Sm; 
 apply plus_lt_compat_l; auto with v62.

intros; unfold double, triple; pattern (q + q) at 1;
 rewrite <- (plus_zero (q + q)); do 2 rewrite plus_n_Sm;
 apply plus_lt_compat_l; auto with v62.
Qed.

Lemma lt_Sdeuxtiersn_n :
 forall n : nat, trois < n -> S (double (tiers n)) < n.
intros n; unfold tiers; case (quotient3 n); intros q He; rewrite He.
case q; unfold double, triple.
simpl; intros; absurd (trois < 0); auto with v62.

clear He q n; intros n; case n.
simpl; intros; absurd (trois < trois); auto with v62.

clear n; intros; rewrite <- (plus_un (S (S n) + S (S n)));
 apply plus_lt_compat_l; unfold un; auto with v62.

case q; unfold double, triple.
simpl; intros; absurd (deux < 0); auto with v62.

clear He n; intros; apply lt_n_S; pattern (S n + S n) at 1;
 rewrite <- (plus_zero (S n + S n)); apply plus_lt_compat_l; 
 auto with v62.

case q; unfold double, triple.
simpl; intros; absurd (un < 0); auto with v62.
do 2 apply lt_S_n; auto with v62.

clear He n; intros; apply lt_n_S; rewrite plus_n_Sm;
 pattern (S n + S n) at 1; rewrite <- (plus_zero (S n + S n));
 apply plus_lt_compat_l; auto with v62.
Qed.

Lemma le_deuxtiers_un : forall a : nat, double (tiers a) <= a.
intros; unfold double, tiers; case (quotient3 a); simpl;
 intros q He; rewrite He; unfold triple; auto with v62.
Qed.

Lemma le_troistiers_un : forall n : nat, triple (tiers n) <= n.
intros; unfold tiers; case (quotient3 n); intros q ->; auto with v62.
Qed.

Lemma lt_O_tiers : forall n : nat, deux < n -> 0 < tiers n.
intros n; unfold tiers; case (quotient3 n); intros q -> **; apply lt_triple.
apply lt_deux_O; assumption.
apply lt_S_n; info_auto with v62.
do 2 apply lt_S_n; auto with v62.
Qed.

Lemma lt_O_deuxtiers : forall n : nat, trois <= n -> 0 < double (tiers n).
unfold double; intros; apply lt_plus_trans; apply lt_O_tiers;
 auto with v62.
Qed.

Lemma Omod3_Unmod3 : forall n : nat, Omod3 n -> Unmod3 (S n).
intros n; unfold Omod3, Unmod3, reste3; simpl;
 case (quotient3 n); simpl; auto with v62.
intros; absurd (2 = 0); auto with v62.
Qed.

Lemma Unmod3_Deuxmod3 : forall n : nat, Unmod3 n -> Deuxmod3 (S n).
intros n; unfold Unmod3, Deuxmod3, reste3; simpl;
 case (quotient3 n); simpl; auto with v62.
intros; absurd (2 = 1); auto with v62.
Qed.

Lemma Deuxmod3_Omod3 : forall n : nat, Deuxmod3 n -> Omod3 (S n).
intros n; unfold Deuxmod3, Omod3, reste3; simpl;
 case (quotient3 n); simpl; auto with v62.
intros; absurd (0 = 2); auto with v62.

intros; absurd (1 = 2); auto with v62.
Qed.

Lemma tiers_S : forall n : nat, Omod3 n -> tiers n = tiers (S n).
intros n; unfold Omod3, reste3, tiers; simpl;
 case (quotient3 n); simpl; auto with v62.
intros; absurd (2 = 0); auto with v62.
Qed.

Lemma tiers_SS : forall n : nat, Unmod3 n -> tiers n = tiers (S n).
intros n; unfold Unmod3, reste3, tiers; simpl;
 case (quotient3 n); simpl; auto with v62.
intros; absurd (2 = 1); auto with v62.
Qed.

Lemma tiers_SSS : forall n : nat, Deuxmod3 n -> S (tiers n) = tiers (S n).
intros n; unfold Deuxmod3, reste3, tiers; simpl;
 case (quotient3 n); simpl; auto with v62.
intros; absurd (0 = 2); auto with v62.

intros; absurd (1 = 2); auto with v62.
Qed.

Lemma le_tiers_trois : forall n : nat, trois <= n -> un <= tiers n.
intros; elim H.
unfold tiers, trois; auto with v62.

intros; apply le_trans with (m := tiers m); auto with v62.
apply le_tiers_Stiers.
Qed.

Lemma le_tiers_six : forall n : nat, six <= n -> deux <= tiers n.
intros; elim H.
unfold tiers, six; auto with v62.

intros; apply le_trans with (m := tiers m); auto with v62.
apply le_tiers_Stiers.
Qed.

End modulo_3.

Section specifique.

Definition Local_Prop := nat -> nat -> Prop.

Definition loi (P Q R T : Local_Prop) :=
  forall t x : nat, P t x -> Q t (S x) -> R t (S (S x)) -> T (S t) (S x).

Definition loi_droite (Q R T : Local_Prop) :=
  forall t x : nat, Q t x -> R t (S x) -> T (S t) x.

Lemma trois_fois_un :
 forall P : nat -> Prop,
 P 0 -> P un -> P deux -> forall n : nat, n <= deux -> P n.
intros P H0 H1 H2 n; case n.
intro; auto with v62.

clear n; intros n; case n.
intro; auto with v62.

clear n; intros n; case n.
intro; auto with v62.

clear n; intros; absurd (S (S (S n)) <= 2); auto with v62.
Qed.

End specifique.

End bibliotheque.
