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

Require Export bib.

Section geometrie.

Section figures.

Inductive Horizontale (t x long : nat) (P : Local_Prop) : Prop :=
    make_horizontale :
      (forall dx : nat, dx <= long -> P t (x + dx)) -> Horizontale t x long P.

Inductive Horizontale_t0 (t x long : nat) (P0 P : Local_Prop) : Prop :=
    make_horizontale_t0 :
      P0 t x -> Horizontale t (S x) long P -> Horizontale_t0 t x long P0 P.

Inductive Horizontale_t1 (t x long : nat) (P0 P1 P : Local_Prop) : Prop :=
    make_horizontale_t1 :
      P0 t x ->
      P1 t (S x) ->
      Horizontale t (S (S x)) long P -> Horizontale_t1 t x long P0 P1 P.

Inductive Verticale (t x haut : nat) (P : Local_Prop) : Prop :=
    make_verticale :
      (forall dt : nat, dt <= haut -> P (t + dt) x) -> Verticale t x haut P.

Inductive Triangle_inf (t x cote : nat) (P : Local_Prop) : Prop :=
    make_triangle_inf :
      (forall dt dx : nat, dx <= cote -> dt <= dx -> P (t + dt) (x + dx)) ->
      Triangle_inf t x cote P.

Inductive Diag (t x cote : nat) (P Q R : Local_Prop) : Prop :=
    make_diag :
      un < cote ->
      P t (x + cote) ->
      (forall dt dx : nat,
       0 < dt -> 0 < dx -> dt + dx = cote -> Q (t + dt) (x + dx)) ->
      R (t + cote) x -> Diag t x cote P Q R.

Inductive Diag' (t x cote : nat) (P Q' Q R : Local_Prop) : Prop :=
    make_diag' :
      deux < cote ->
      P t (x + cote) ->
      (forall dx : nat, dx + un = cote -> Q' (t + un) (x + dx)) ->
      (forall dt dx : nat,
       un < dt -> 0 < dx -> dt + dx = cote -> Q (t + dt) (x + dx)) ->
      R (t + cote) x -> Diag' t x cote P Q' Q R.

Inductive Semi_Diag (t x cote : nat) (P Q : Local_Prop) : Prop :=
    make_semidiag :
      0 < cote ->
      P t (x + cote) ->
      (forall dt dx : nat, 0 < dt -> dt + dx = cote -> Q (t + dt) (x + dx)) ->
      Semi_Diag t x cote P Q.

End figures.

Section principes.

Notation rec4 := (Rec4 _ _ _ _ _) (only parsing).

Notation rec5 := (Rec5 _ _ _ _ _ _) (only parsing).

Fact inter :
 forall (a b long : nat) (T : Local_Prop),
 (forall dx : nat, b < dx -> S a + dx = long -> T (S a) dx) ->
 (forall dt dx : nat,
  a < dt ->
  b < dx -> S dt + S dx = long -> T dt (S (S dx)) -> T (S dt) (S dx)) ->
 (forall dt : nat,
  a < dt -> S dt + S b = long -> T dt (S (S b)) -> T (S dt) (S b)) ->
 forall dt dx : nat, a < dt -> b < dx -> dt + dx = long -> T dt dx.
intros a b long T H1 H2 H3 dt dx Hlt; generalize dx; clear dx; elim Hlt;
 auto with v62.
clear Hlt dt; intros dt Hle Hr dx Hgt; case Hgt; intros.
apply H3; auto with v62.
apply Hr; auto with v62.
rewrite <- plus_Snm_nSm; auto with v62.

apply H2; auto with v62.
apply Hr; auto with v62.
rewrite <- plus_Snm_nSm; auto with v62.
Qed.

Lemma Rec_Diag :
 forall (t x cote : nat) (P Q R : Local_Prop),
 un < cote ->
 P t (x + cote) ->
 (forall dx : nat,
  dx + deux = cote -> P t (x + cote) -> Q (t + un) (x + S dx)) ->
 (forall dt dx : nat,
  0 < dt ->
  0 < dx ->
  S dt + S dx = cote -> Q (t + dt) (x + S (S dx)) -> Q (t + S dt) (x + S dx)) ->
 (forall dt : nat,
  dt + deux = cote -> Q (t + dt) (x + deux) -> Q (t + S dt) (x + un)) ->
 (forall dt : nat, dt + un = cote -> Q (t + dt) (x + un) -> R (t + cote) x) ->
 Diag t x cote P Q R.
intros; apply (Rec4 _ _ _ _ _ (make_diag t x cote P Q R)); auto with v62.
intros; apply (inter 0 0 cote (fun dt dx : nat => Q (t + dt) (x + dx)));
 auto with v62.
intros dx0 Hlt; rewrite (S_pred dx0); simpl in |- *; intros; auto with v62.
apply H1; auto with v62.
rewrite plus_deux; auto with v62.

intros; apply H3; auto with v62.
rewrite <- H10; rewrite plus_un; rewrite plus_deux; auto with v62.

intros; apply (H4 (pred cote)); auto with v62.
rewrite plus_un; rewrite <- S_pred; auto with v62.

apply H5; auto with v62.
rewrite plus_un; rewrite <- S_pred; auto with v62.
Qed.

Lemma Rec_Diag' :
 forall (t x cote : nat) (P Q' Q R : Local_Prop),
 deux < cote ->
 P t (x + cote) ->
 (forall dx : nat,
  dx + deux = cote -> P t (x + cote) -> Q' (t + un) (x + S dx)) ->
 (forall dx : nat,
  dx + trois = cote -> Q' (t + un) (x + S (S dx)) -> Q (t + deux) (x + S dx)) ->
 (forall dt dx : nat,
  un < dt ->
  0 < dx ->
  S dt + S dx = cote -> Q (t + dt) (x + S (S dx)) -> Q (t + S dt) (x + S dx)) ->
 (forall dt : nat,
  dt + deux = cote -> Q (t + dt) (x + deux) -> Q (t + S dt) (x + un)) ->
 (forall dt : nat, dt + un = cote -> Q (t + dt) (x + un) -> R (t + cote) x) ->
 Diag' t x cote P Q' Q R.
intros; apply (Rec5 _ _ _ _ _ _ (make_diag' t x cote P Q' Q R));
 auto with v62.
intros H6 dx; rewrite (plus_un dx); intros H7; generalize H7;
 rewrite (S_pred dx); intros; auto with v62.
apply H1; auto with v62.
rewrite plus_deux; auto with v62.

apply lt_S_n; rewrite H7; auto with v62.

intros; apply (inter un 0 cote (fun dt dx : nat => Q (t + dt) (x + dx)));
 auto with v62.
intros dx0 Hlt; rewrite (S_pred dx0); unfold un in |- *; simpl in |- *;
 intros; auto with v62.
apply H2; auto with v62.
rewrite plus_trois; auto with v62.

apply H6; auto with v62.
rewrite plus_un; auto with v62.

intros dt0; rewrite plus_un; intros; apply H4; auto with v62.
rewrite plus_deux; auto with v62.

intros; apply (H5 (pred cote)); auto with v62.
rewrite plus_un; rewrite <- S_pred; auto with v62.
apply lt_deux_O; auto with v62.

apply H6; auto with v62.
rewrite plus_un; rewrite <- S_pred; auto with v62.
apply lt_deux_O; auto with v62.
Qed.

Lemma Rec_SemiDiag :
 forall (t x cote : nat) (P Q : Local_Prop),
 0 < cote ->
 P t (x + cote) ->
 (forall dx : nat, un + dx = cote -> P t (x + cote) -> Q (t + un) (x + dx)) ->
 (forall dt dx : nat,
  0 < dt ->
  S dt + dx = cote -> Q (t + dt) (x + S dx) -> Q (t + S dt) (x + dx)) ->
 Semi_Diag t x cote P Q.
intros; apply make_semidiag; auto with v62.
intros dt dx Hlt; generalize dx; elim Hlt.
intros; apply H1; auto with v62.

intros; apply H2; auto with v62.
apply H4; auto with v62.
rewrite <- plus_Snm_nSm; auto with v62.
Qed.

Lemma deux_Diag :
 forall (P Q : Local_Prop) (t x : nat),
 P t (S (S x)) -> Q (S t) (S x) -> P (S (S t)) x -> Diag t x deux P Q P.
intros; apply make_diag.
auto with v62.

rewrite plus_deux; auto with v62.

intros dt dx Hl; generalize dx; clear dx; case Hl.
intros dx Hg; case Hg.
intro; repeat rewrite plus_un; auto with v62.

simpl in |- *; unfold deux in |- *; intros; absurd (0 = m); auto with v62.
injection H3; auto with v62.

unfold deux in |- *; simpl in |- *; intros; absurd (1 < m + dx).
injection H4; intros H5; rewrite H5; auto with v62.

apply le_lt_trans with (m := m + 0); auto with v62.

rewrite plus_deux; auto with v62.
Qed.

Lemma rec_triangle_inf :
 forall (t x cote : nat) (P : Local_Prop),
 Horizontale t x cote P ->
 (forall t' x' : nat, P t' x' -> P t' (S x') -> P (S t') (S x')) ->
 Triangle_inf t x cote P.
intros; elim H; clear H; intros; apply make_triangle_inf.
simple induction dt; intros.
rewrite plus_zero; auto with v62.

generalize H2 H3 (H1 dx); elim dx; intros.
absurd (S n <= 0); auto with v62.

do 2 rewrite <- plus_n_Sm; apply H0.
apply H1; auto with v62.

rewrite plus_n_Sm; apply H7; auto with v62.
Qed.

Lemma inclus_vert :
 forall (t t' x haut haut' : nat) (P : Local_Prop),
 t <= t' ->
 t' + haut' <= t + haut -> Verticale t x haut P -> Verticale t' x haut' P.
intros; apply make_verticale; intros.
elim H1; intros.
generalize (H3 (t' - t + dt)).
rewrite plus_assoc.
rewrite le_plus_minus_r; auto with v62.
intros; apply H4.
apply (fun p n m : nat => plus_le_reg_l n m p) with (p := t).
rewrite plus_assoc.
rewrite le_plus_minus_r; auto with v62.
apply le_trans with (m := t' + haut'); auto with v62.
Qed.

Lemma vv_vert :
 forall (t x haut haut' : nat) (P : Local_Prop),
 Verticale t x haut P ->
 Verticale (t + S haut) x haut' P -> Verticale t x (S haut + haut') P.
intros; apply make_verticale; intros; case (le_lt_dec dt haut).
elim H; auto with v62.

elim H0; intros; generalize (H2 (dt - S haut)).
rewrite plus_assoc_reverse; rewrite le_plus_minus_r; auto with v62.
intros; apply H3;
 apply (fun p n m : nat => plus_le_reg_l n m p) with (p := S haut);
 rewrite le_plus_minus_r; auto with v62.
Qed.

Lemma rec_vert :
 forall (t x haut : nat) (P : Local_Prop),
 (forall dt : nat,
  dt <= haut -> P (t + double dt) x /\ P (t + S (double dt)) x) ->
 Verticale t x (S (double haut)) P.
intros; apply make_verticale; intros.
elim (quotient2 dt); intros.
rewrite e0; elim (H q); intros; auto with v62.
apply le_S_double; rewrite <- e0; auto with v62.

rewrite e; elim (H q); intros; auto with v62.
apply le_double; apply le_S_n; rewrite <- e; auto with v62.
Qed.

Lemma vert_un :
 forall (t x : nat) (P : Local_Prop),
 P t x -> P (S t) x -> Verticale t x un P.
intros; apply make_verticale; intros dt; case dt.
intros; rewrite plus_zero; auto with v62.

clear dt; intros dt; case dt.
intros; rewrite plus_un; auto with v62.

intros; absurd (S (S n) <= 1); auto with v62.
Qed.

Lemma vert_deux :
 forall (t x : nat) (P : Local_Prop),
 P t x -> P (S t) x -> P (S (S t)) x -> Verticale t x deux P.
intros; apply make_verticale; intros dt; case dt.
intros; rewrite plus_zero; auto with v62.

clear dt; intros dt; case dt.
intros; rewrite plus_un; auto with v62.

clear dt; intros dt; case dt.
intros; rewrite plus_deux; auto with v62.

intros; absurd (S (S (S n)) <= 2); auto with v62.
Qed.

Lemma vert_trois :
 forall (t x : nat) (P : Local_Prop),
 P t x ->
 P (S t) x -> P (S (S t)) x -> P (S (S (S t))) x -> Verticale t x trois P.
intros; apply make_verticale; intros dt; case dt.
intros; rewrite plus_zero; auto with v62.

clear dt; intros dt; case dt.
intros; rewrite plus_un; auto with v62.

clear dt; intros dt; case dt.
intros; rewrite plus_deux; auto with v62.

clear dt; intros dt; case dt.
intros; rewrite plus_trois; auto with v62.

intros; absurd (S (S (S (S n))) <= 3); auto with v62.
Qed.

Lemma hh_hor :
 forall (t x cote cote' : nat) (P : Local_Prop),
 Horizontale t x cote P ->
 Horizontale t (x + S cote) cote' P -> Horizontale t x (S cote + cote') P.
intros; apply make_horizontale.
intros dx; case (le_gt_dec dx cote).
intros; elim H; auto with v62.

intros; elim H0; intros.
replace dx with (S cote + (dx - S cote)).
rewrite plus_assoc; apply H2.
apply (fun p n m : nat => plus_le_reg_l n m p) with (p := S cote).
rewrite le_plus_minus_r; auto with v62.

rewrite le_plus_minus_r; auto with v62.
Qed.

Lemma hor_un :
 forall (t x : nat) (P : Local_Prop),
 P t x -> P t (S x) -> Horizontale t x un P.
intros; apply make_horizontale; intros dx; case dx.
intros; rewrite plus_zero; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_un; auto with v62.

intros; absurd (S (S n) <= 1); auto with v62.
Qed.

Lemma hor_deux :
 forall (t x : nat) (P : Local_Prop),
 P t x -> P t (S x) -> P t (S (S x)) -> Horizontale t x deux P.
intros; apply make_horizontale; intros dx; case dx.
intros; rewrite plus_zero; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_un; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_deux; auto with v62.

intros; absurd (S (S (S n)) <= 2); auto with v62.
Qed.

Lemma hor_trois :
 forall (t x : nat) (P : Local_Prop),
 P t x ->
 P t (S x) -> P t (S (S x)) -> P t (S (S (S x))) -> Horizontale t x trois P.
intros; apply make_horizontale; intros dx; case dx.
intros; rewrite plus_zero; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_un; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_deux; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_trois; auto with v62.

intros; absurd (S (S (S (S n))) <= 3); auto with v62.
Qed.

Lemma hor_quatre :
 forall (t x : nat) (P : Local_Prop),
 P t x ->
 P t (S x) ->
 P t (S (S x)) ->
 P t (S (S (S x))) -> P t (S (S (S (S x)))) -> Horizontale t x quatre P.
intros; apply make_horizontale; intros dx; case dx.
intros; rewrite plus_zero; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_un; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_deux; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_trois; auto with v62.

clear dx; intros dx; case dx.
intros; rewrite plus_quatre; auto with v62.

intros; absurd (S (S (S (S (S n)))) <= 4); auto with v62.
apply lt_not_le; repeat apply lt_n_S; auto with v62.
Qed.

End principes.

End geometrie.
