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

Require Export double_diag.

Section verticale.

Notation rec2 := (Rec2 _ _ _) (only parsing).

Notation rec3 := (Rec3 _ _ _ _) (only parsing).

Notation rec3' := (Rec3' _ _ _ _) (only parsing).

Section triangle_inferieur.

Lemma Ht1_End2 :
 forall t x long : nat,
 Horizontale_t1 t x long G_Etat C_Etat L_Etat -> deux_end t x.
intros t x long H; elim H; clear H; intros H H0 H1;
 apply (Rec3 _ _ _ _ (make_deux_end t x)); auto with v62.
apply (GC_dollarB t x); auto with v62.

intros; apply (Rec2 _ _ _ (make_un_end (S t) x)).
apply GC_G; auto with v62.

intros; apply GB_G; auto with v62.
Qed.

Lemma Ht1_End4 :
 forall t x long : nat,
 0 < long -> Horizontale_t1 t x long G_Etat C_Etat L_Etat -> quatre_end t x.
intros; elim (Ht1_End2 t x long); unfold B_Etat; intros;
 auto with v62.
elim H0; clear H0 H1; unfold L_Etat, C_Etat; intros H0 H1 H4; elim H4;
 clear H4; intros H4.
generalize (H4 0); rewrite plus_zero; intros.
generalize (H4 un); rewrite plus_un; intros.
apply (Rec3 _ _ _ _ (make_quatre_end t x)); unfold L_Etat;
 auto with v62.
rewrite un_pas; rewrite H5; try rewrite H6; auto with v62.

intros; apply (Rec3' _ _ _ _ (make_trois_end (S t) x)); auto with v62.
unfold A_Etat; rewrite un_pas; rewrite H1; rewrite H5; try rewrite H6;
 auto with v62.

unfold A_Etat, G_Etat; intros; rewrite un_pas; rewrite H2; rewrite H8;
 rewrite H7; auto with v62.

elim H3; clear H0 H1 H3 H4 H5 H6; intros;
 apply (Rec3' _ _ _ _ (make_deux_end (S (S t)) x)).
apply GBA_dollarC; auto with v62.

intros; apply (GC_dollarB (S (S t)) x); auto with v62.

clear H0 H2 H3 H4 H7; intros;
 apply (Rec2 _ _ _ (make_un_end (S (S (S t))) x)).
apply GC_G; auto with v62.

intros; apply GB_G; auto with v62.
Qed.

Lemma Hor_tr_inf :
 forall t x cote : nat,
 Horizontale t x cote L_Etat -> Triangle_inf t x cote L_Etat.
intros; apply rec_triangle_inf; auto with v62.
unfold L_Etat; intros; rewrite un_pas; rewrite H0; rewrite H1;
 auto with v62.
Qed.

End triangle_inferieur.

Section triangle_median.

Lemma Ht1_bissect :
 forall t x cote : nat,
 0 < cote ->
 Horizontale_t1 t x cote G_Etat C_Etat L_Etat ->
 forall dx : nat,
 S dx <= cote ->
 L_Etat (t + dx) (S (S x) + S dx) /\ L_Etat (t + S dx) (S (S x) + S dx).
intros; elim (Hor_tr_inf t (S (S x)) cote); intros; split; auto with v62.
elim H0; intros; elim H4; auto with v62.
Qed.

Theorem Ht1_DD :
 forall t x cote : nat,
 0 < cote ->
 Horizontale_t1 t x cote G_Etat C_Etat L_Etat ->
 forall dx : nat, S dx <= cote -> DD (t + dx) x (S (S (S dx))).
intros t x cote H H0 dx; elim dx; intros.
rewrite plus_zero; apply DD_4; apply Ht1_End4 with (long := cote);
 auto with v62.

elim (Ht1_bissect t x cote) with (dx := S n); auto with v62; intros.
rewrite <- plus_n_Sm; apply DD_hddollar; auto with v62.
do 2 rewrite <- plus_Snm_nSm; rewrite plus_n_Sm; auto with v62.

do 2 rewrite <- plus_Snm_nSm; do 2 rewrite plus_n_Sm; auto with v62.
Qed.

Lemma Ht1_DDf :
 forall t x haut : nat,
 Horizontale_t1 t x (S haut) G_Etat C_Etat L_Etat ->
 DD (t + haut) x (S (S (S haut))).
intros; apply (Ht1_DD t x (S haut)); auto with v62.
Qed.

Lemma Ht1_VV :
 forall t x cote : nat,
 Horizontale_t1 t x cote G_Etat C_Etat L_Etat ->
 Verticale (S t) x (S (double cote)) G_Etat.
intros; apply rec_vert.
intros dt; case dt; intros.
unfold double; repeat rewrite plus_zero; rewrite plus_un;
 apply deux_GG.
apply Ht1_End2 with (long := cote); auto with v62.

rewrite <- plus_n_Sm; rewrite plus_Snm_nSm; unfold double.
rewrite (plus_n_Sm (S n) (S n)); rewrite plus_Snm_nSm; rewrite plus_assoc.
apply DD_GG; apply Ht1_DD with (cote := cote); auto with v62.
apply lt_le_trans with (m := S n); auto with v62.
Qed.

End triangle_median.

Section triangle_base.

Variable t long : nat.

Hypothesis Assez_grand : un < long.

Hypothesis Base : Horizontale_t0 t 0 long G_Etat L_Etat.

Lemma Ht0_bissect :
 forall dx : nat,
 S dx <= long -> L_Etat (t + dx) (S (S dx)) /\ L_Etat (t + S dx) (S (S dx)).
intros; elim (Hor_tr_inf t 1 long); simpl; intros; split;
 auto with v62.
elim Base; intros; elim H1; auto with v62.
Qed.

Remark A10 : Etat (S t) 0 = A.
elim Base; unfold L_Etat, G_Etat; intros; elim H0; intros.
generalize (H1 0); simpl; intros.
rewrite H; rewrite H2; auto with v62.
Qed.

Remark C11 : Etat (S t) 1 = C.
elim Base; unfold L_Etat, G_Etat; intros; elim H0; intros.
generalize (H1 0); simpl; intros.
generalize (H1 1); simpl; intros.
rewrite H; rewrite H2; try rewrite H3; auto with v62.
Qed.

Remark G20 : Etat (S (S t)) 0 = G.
rewrite demi_pas; rewrite A10; rewrite C11; auto with v62.
Qed.

Remark B21 : Etat (S (S t)) 1 = B.
rewrite un_pas; rewrite A10; rewrite C11; auto with v62.
Qed.

Lemma Ht0_End2 : deux_end (S t) 0.
apply make_deux_end.
unfold C_Etat; apply C11.

unfold B_Etat; apply B21.

apply make_un_end.
unfold G_Etat; apply G20.

apply GB_G.
unfold G_Etat; apply G20.

unfold B_Etat; apply B21.
Qed.

Lemma Ht0_End4 : quatre_end (S t) 0.
apply deux_quatre.
apply Ht0_End2.

generalize (Ht0_bissect 0); rewrite plus_un; intros H; elim H; auto with v62.

generalize (Ht0_bissect 1); rewrite plus_un; intros H; elim H; auto with v62.

generalize (Ht0_bissect 1); rewrite plus_deux; intros H; elim H;
 auto with v62.
Qed.

Theorem Ht0_DD :
 forall dx : nat, S (S dx) <= long -> DD (S t + dx) 0 (S (S (S dx))).
simple induction dx; intros.
rewrite plus_zero; apply DD_4; apply Ht0_End4.

rewrite <- plus_n_Sm; apply DD_hddollar; auto with v62.
simpl; do 2 rewrite plus_n_Sm; elim (Ht0_bissect (S (S n)));
 auto with v62.

simpl; do 3 rewrite plus_n_Sm; elim (Ht0_bissect (S (S n)));
 auto with v62.
Qed.

Lemma Ht0_DDf : DD (t + pred long) 0 (S long).
generalize (Ht0_DD (pred (pred long))); rewrite plus_Snm_nSm;
 repeat rewrite <- S_pred; auto with v62.
Qed.

End triangle_base.

End verticale.