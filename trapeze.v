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

Require Export reflection.
Require Export vertical.

Section trapezes.

Lemma R1 : forall n : nat, un < n -> double n = 3 + S (double (S n - trois)).
intros; rewrite minus_trois; simpl; unfold double.
do 2 rewrite plus_n_Sm; do 2 rewrite <- plus_S; rewrite <- SS_pred;
 auto with arith.
Qed.

Lemma R1' :
 forall n : nat, un < n -> pred (double n) = 2 + S (double (S n - trois)).
intros; rewrite minus_trois; simpl; unfold double.
apply eq_add_S; do 2 rewrite plus_n_Sm; do 2 rewrite <- plus_S;
 rewrite <- SS_pred; auto with arith.
rewrite <- S_pred; auto with arith.
Qed.

Lemma R2 : forall n : nat, deux < n -> 0 < S n - trois.
unfold deux; intros; rewrite minus_trois; simpl.
do 2 (apply lt_S_n; rewrite <- S_pred; auto with arith).
apply lt_trans with (m := un); auto with arith.
Qed.

Lemma R3 : forall n : nat, deux < n -> n = S (S (S (pred (S n - trois)))).
intros; rewrite minus_trois; simpl; rewrite <- minus_trois;
 rewrite SSSminus_trois; auto with arith.
Qed.

Section deux_trapeze.

Variable t x : nat.

Hypothesis Hh : Horizontale_t1 t x 0 G_Etat C_Etat L_Etat.

Hypothesis Hv : Verticale t (S (S (S x))) deux G_Etat.

Lemma H2_Vg : Verticale (S t) x un G_Etat.
replace un with (S (double 0)); auto with arith.
apply Ht1_VV; auto with arith.
Qed.

Lemma H2_Hh : Horizontale_t1 (S t) x 0 G_Etat B_Etat G_Etat.
elim (Ht1_End2 t x 0); auto with arith; intros; elim H1; intros.
apply make_horizontale_t1; auto with arith.
clear H0 H1 H2 H3; apply make_horizontale; intros dx; case dx; intros.
rewrite plus_zero; unfold G_Etat; rewrite un_pas.
elim Hh; elim Hv; clear Hh Hv; intros; elim H4; clear H2 H3 H4; intros.
generalize (H1 0); rewrite plus_zero; unfold G_Etat; intros.
generalize (H2 0); rewrite plus_zero; unfold L_Etat; intros.
unfold C_Etat in H; rewrite H; rewrite H3; try rewrite H4; auto with arith.

absurd (S n <= 0); auto with arith.
Qed.

Lemma H2_Hg : Horizontale (S (S t)) x deux G_Etat.
elim H2_Hh; intros; elim H1; intros; generalize (H2 0); rewrite plus_zero;
 intros; apply hor_deux.
apply GB_G; auto with arith.

apply (GBG_dollarG (S t) x); auto with arith.

elim Hv; intros; generalize (H4 un); rewrite plus_un; unfold G_Etat;
 intros.
rewrite un_pas; unfold B_Etat in H0; rewrite H0; unfold G_Etat in H3;
 rewrite H3; try rewrite H5; auto with arith.
Qed.

End deux_trapeze.

Section A_trapeze.

Lemma Ha_Vg :
 forall t x cote : nat,
 A_basic t x (S cote) ->
 Verticale (S t) (S (x + S cote)) (triple cote) G_Etat ->
 Verticale (S (t + S cote)) (S x) (pred (double cote)) G_Etat.
intros; rewrite R1'.
elim (A_ZCB t x (S cote)); auto with arith; intros.
apply vv_vert.
rewrite <- plus_S; apply A_Vg; auto with arith.
elim H2; auto with arith.

elim H3; auto with arith.

rewrite plus_deux; apply Ht1_VV.
rewrite <- plus_S; rewrite plus_n_Sm; apply ZCB_Ht1.
elim H; auto with arith.

apply make_ZCB; auto with arith.

apply inclus_vert with (t := S t) (haut := triple cote); auto with arith.
do 2 rewrite plus_Snm_nSm; apply plus_le_compat_l; elim H; intros.
apply le_SSS_triple; auto with arith.

elim H0; intros; rewrite <- (plus_zero (S t)); apply H1; auto with arith.

elim H0; intros; rewrite <- (plus_un (S t)); apply H1; auto with arith.
elim H; intros; apply le_n_triplem; apply le_S_n; auto with arith.

elim H; auto with arith.
Qed.

Lemma Ha3_Hg :
 forall t x : nat,
 A_basic t x trois ->
 Verticale (S t) (x + quatre) six G_Etat ->
 Horizontale (t + sept) (S x) deux G_Etat.
intros; rewrite plus_sept; apply H2_Hg.
rewrite (minus_n_n trois); rewrite <- (plus_quatre (S t));
 unfold quatre; apply ZCB_Ht1; auto with arith.
elim H0; intros; apply A_ZCB; auto with arith.
rewrite plus_Snm_nSm; rewrite <- (plus_zero (S t)); apply H1; auto with arith.

rewrite plus_Snm_nSm; rewrite <- (plus_un (S t)); apply H1;
 unfold un, six; auto with arith.

rewrite plus_Snm_nSm; apply inclus_vert with (t := S t) (haut := six);
 auto with arith.
rewrite plus_trois; rewrite plus_six; auto with arith.

rewrite <- (plus_quatre x); apply inclus_vert with (t := S t) (haut := six);
 auto with arith.
rewrite plus_deux; rewrite plus_six; auto with arith.
Qed.

Lemma Ha_DD :
 forall t x cote : nat,
 deux < cote ->
 A_basic t x (S cote) ->
 Verticale (S t) (S (x + S cote)) (triple cote) G_Etat ->
 DD (t + double cote) (S x) cote.
intros; unfold double.
pattern cote at 2 3; rewrite (R3 cote); auto with arith.
do 3 rewrite <- plus_Snm_nSm; rewrite plus_assoc;
 apply Ht1_DD with (cote := S cote - trois).
apply R2; auto with arith.

rewrite <- plus_Snm_nSm; apply ZCB_Ht1; auto with arith.
elim H1; intros; apply A_ZCB; auto with arith.
rewrite <- (plus_zero (S t)); apply H2; auto with arith.

rewrite <- (plus_un (S t)); apply H2; auto with arith.
apply le_n_triplem; apply le_trans with (m := deux); auto with arith.

apply inclus_vert with (t := S t) (haut := triple cote); auto with arith.
do 2 rewrite plus_Snm_nSm; apply plus_le_compat_l;
 rewrite <- (plus_trois cote); unfold triple;
 rewrite plus_assoc_reverse; apply plus_le_compat_l;
 apply le_trans with (m := deux + deux); auto with arith.
apply plus_le_compat; auto with arith.

rewrite <- S_pred; auto with arith.
apply R2; auto with arith.
Qed.

End A_trapeze.

Section B_trapeze.

Lemma Hb_Vg :
 forall t x cote : nat,
 B_basic t x (S cote) ->
 Verticale (S t) (S (x + S cote)) (S (triple cote)) G_Etat ->
 Verticale (S (t + S cote)) (S x) (double cote) G_Etat.
intros; rewrite R1.
apply vv_vert.
elim H0; intros; rewrite <- plus_S; apply B_Vg; auto with arith.
rewrite <- (plus_zero (S t)); apply H1; auto with arith.

rewrite <- (plus_un (S t)); apply H1; auto with arith.
elim H; intros; unfold un; apply le_n_S; apply le_n_triplem;
 auto with arith.

rewrite <- (plus_deux (S t)); apply H1; auto with arith.
elim H; intros; unfold deux; apply le_n_S; apply le_n_triplem;
 apply le_S_n; auto with arith.

rewrite plus_trois; apply Ht1_VV.
do 2 rewrite <- plus_S; rewrite plus_n_Sm; apply ZCB_Ht1.
elim H; auto with arith.

elim H0; intros; apply B_ZCB; auto with arith.
rewrite <- (plus_zero (S t)); apply H1; auto with arith.

rewrite <- (plus_un (S t)); apply H1; auto with arith.
unfold un; apply le_n_S; apply le_n_triplem; auto with arith.

rewrite <- (plus_deux (S t)); apply H1; auto with arith.
elim H; intros; unfold deux; apply le_n_S; apply le_n_triplem;
 apply le_S_n; auto with arith.

apply inclus_vert with (t := S t) (haut := S (triple cote)); auto with arith.
do 3 rewrite plus_Snm_nSm; apply plus_le_compat_l; apply le_n_S; elim H;
 intros.
apply le_SSS_triple; auto with arith.

elim H; auto with arith.
Qed.

Lemma Hb3_Hg :
 forall t x : nat,
 B_basic t x trois ->
 Verticale (S t) (x + quatre) sept G_Etat ->
 Horizontale (t + huit) (S x) deux G_Etat.
intros; rewrite plus_huit; apply H2_Hg.
rewrite (minus_n_n trois); rewrite <- (plus_quatre (S (S t)));
 unfold quatre; apply ZCB_Ht1; auto with arith.
elim H0; intros; apply B_ZCB; auto with arith.
rewrite plus_Snm_nSm; rewrite <- (plus_zero (S t)); apply H1; auto with arith.

rewrite plus_Snm_nSm; rewrite <- (plus_un (S t)); apply H1;
 unfold un, sept; auto with arith.

rewrite plus_Snm_nSm; rewrite <- (plus_deux (S t)); apply H1;
 unfold deux, sept; auto with arith.

rewrite plus_Snm_nSm; apply inclus_vert with (t := S t) (haut := sept);
 auto with arith.
rewrite plus_trois; rewrite plus_sept; auto with arith.

rewrite <- (plus_quatre x); apply inclus_vert with (t := S t) (haut := sept);
 auto with arith.
rewrite plus_deux; rewrite plus_sept; auto with arith.
Qed.

Lemma Hb_DD :
 forall t x cote : nat,
 deux < cote ->
 B_basic t x (S cote) ->
 Verticale (S t) (S (x + S cote)) (S (triple cote)) G_Etat ->
 DD (t + S (double cote)) (S x) cote.
intros; unfold double; pattern cote at 2 3; rewrite (R3 cote);
 auto with arith.
rewrite <- plus_S; do 3 rewrite <- plus_Snm_nSm; rewrite plus_assoc;
 apply Ht1_DD with (cote := S cote - trois); auto with arith.
apply R2; auto with arith.

do 2 rewrite <- plus_Snm_nSm; apply ZCB_Ht1; auto with arith.
elim H1; intros; apply B_ZCB; auto with arith.
rewrite <- (plus_zero (S t)); apply H2; auto with arith.

rewrite <- (plus_un (S t)); apply H2; auto with arith.
unfold un; apply le_n_S; apply le_n_triplem;
 apply le_trans with (m := deux); auto with arith.

rewrite <- (plus_deux (S t)); apply H2; auto with arith.
unfold deux; apply le_n_S; apply le_n_triplem;
 apply le_trans with (m := deux); auto with arith.

apply inclus_vert with (t := S t) (haut := S (triple cote)); auto with arith.
do 3 rewrite plus_Snm_nSm; apply plus_le_compat_l;
 rewrite <- (plus_quatre cote); unfold triple;
 rewrite plus_assoc_reverse; rewrite plus_n_Sm; apply plus_le_compat_l;
 apply le_trans with (m := deux + deux); auto with arith.
rewrite <- plus_S; apply plus_le_compat; auto with arith.

rewrite <- S_pred; auto with arith; apply R2; auto with arith.
Qed.

End B_trapeze.

Section C_trapeze.

Section Cas_particulier.

Variable t x : nat.

Hypothesis Hc : C_basic t x deux.

Hypothesis Hv : Verticale (S t) (x + trois) cinq G_Etat.

Lemma G22 : G_Etat (S (S t)) (S (S x)).
elim Hc; elim Hv; clear Hc Hv; intros.
generalize (H 0); clear H; rewrite plus_zero; rewrite plus_trois;
 unfold G_Etat; intros.
elim H1; elim H2; clear H1 H2; unfold L_Etat, C_Etat;
 rewrite plus_deux; intros.
generalize (H7 un un); clear H3 H4 H5 H6 H7 H8; do 3 rewrite plus_un; intros.
rewrite un_pas; rewrite H2; rewrite H; try rewrite H3; auto with arith. 
Qed.

Lemma G31 : G_Etat (S (S (S t))) (S x).
elim Hc; intros.
elim H0; elim H1; clear H0 H1; unfold L_Etat, C_Etat;
 repeat rewrite plus_deux; intros.
generalize (H2 un un); clear H0 H1 H2 H3 H4 H5 H6; do 3 rewrite plus_un;
 intros.
generalize G22; unfold G_Etat; intros; rewrite un_pas; rewrite H0;
 auto with arith.
rewrite H1; rewrite H7; auto with arith.
Qed.

Lemma A32 : A_Etat (S (S (S t))) (S (S x)).
elim Hc; elim Hv; generalize G22; clear Hc Hv;
 unfold A_Etat, C_Etat, G_Etat; intros.
generalize (H0 un); clear H0; rewrite plus_un; rewrite plus_trois; intros.
elim H3; clear H1 H2 H3; intros.
generalize (H3 un un); clear H1 H2 H3 H4; do 3 rewrite plus_un; intros.
rewrite un_pas; rewrite H; rewrite H0; try rewrite H1;
 unfold un, cinq; auto with arith.
Qed.

Lemma G41 : G_Etat (S (S (S (S t)))) (S x).
apply GA_G.
apply G31.

apply A32.
Qed.

Lemma C42 : C_Etat (S (S (S (S t)))) (S (S x)).
apply (GA_dollarC (S (S (S t))) (S x)); auto with arith.
apply G31.

apply A32.
Qed.

Lemma G51 : G_Etat (S (S (S (S (S t))))) (S x).
apply GC_G.
apply G41.

apply C42.
Qed.

Lemma B52 : B_Etat (S (S (S (S (S t))))) (S (S x)).
apply (GC_dollarB (S (S (S (S t)))) (S x)); auto with arith.
apply G41.

apply C42.
Qed.

Lemma Hc2_Vg : Verticale (t + trois) (S x) trois G_Etat.
rewrite plus_trois; apply vert_trois.
apply G31.

apply G41.

apply G51.

apply GB_G.
apply G51.

apply B52.
Qed.

Lemma Hc2_Hg : Horizontale (t + six) (S x) un G_Etat.
rewrite plus_six; apply hor_un.
apply GB_G.
apply G51.

apply B52.

apply GBG_dollarG.
apply G51.

apply B52.

elim Hv; rewrite plus_trois; intros.
generalize (H quatre); rewrite plus_quatre; auto with arith.
Qed.

End Cas_particulier.

Lemma R5 :
 forall P : nat -> Prop,
 P un -> (forall n : nat, un < n -> P n) -> forall n : nat, 0 < n -> P n.
intros; case H1; auto with arith.
Qed.

Lemma Hc_Vg :
 forall t x cote : nat,
 C_basic t x (S cote) ->
 Verticale (S t) (S (x + S cote)) (S (S (triple cote))) G_Etat ->
 Verticale (S (t + S cote)) (S x) (S (double cote)) G_Etat.
intros t x cote Hc; generalize Hc; apply R5 with (n := cote).
do 2 rewrite plus_n_Sm; unfold double, triple, un;
 repeat rewrite plus_un; intros; apply Hc2_Vg; auto with arith.

clear Hc cote; intros cote Hlt H H0; rewrite (R1 cote); auto with arith.
rewrite <- (plus_S 3); apply vv_vert.
elim H0; intros; rewrite <- plus_S; apply C_Vg.
unfold deux; apply lt_n_S; auto with arith.

auto with arith.

rewrite <- (plus_zero (S t)); apply H1; auto with arith.

rewrite <- (plus_un (S t)); apply H1; auto with arith.
unfold un; apply le_n_S; apply le_S; apply le_n_triplem;
 auto with arith.

rewrite <- (plus_deux (S t)); apply H1; auto with arith.
unfold deux; do 2 apply le_n_S; apply le_n_triplem; auto with arith.

rewrite <- (plus_trois (S t)); apply H1; auto with arith.
unfold trois; do 2 apply le_n_S; apply le_n_triplem; auto with arith.

rewrite plus_quatre; apply Ht1_VV.
do 3 rewrite <- plus_S; rewrite plus_n_Sm; apply ZCB_Ht1.
unfold deux; apply lt_n_S; auto with arith.

elim H0; intros; apply C_ZCB; auto with arith.
rewrite <- (plus_zero (S t)); apply H1; auto with arith.

rewrite <- (plus_un (S t)); apply H1; auto with arith.
unfold un; apply le_n_S; apply le_S; apply le_n_triplem;
 auto with arith.

rewrite <- (plus_deux (S t)); apply H1; auto with arith.
unfold deux; do 2 apply le_n_S; apply le_n_triplem; auto with arith.

rewrite <- (plus_trois (S t)); apply H1; auto with arith.
unfold trois; do 2 apply le_n_S; apply le_n_triplem; auto with arith.

apply inclus_vert with (t := S t) (haut := S (S (triple cote)));
 auto with arith.
do 4 rewrite plus_Snm_nSm; apply plus_le_compat_l; do 2 apply le_n_S;
 apply le_SSS_triple; auto with arith.

elim Hc; auto with arith.
Qed.

Lemma Hc3_Hg :
 forall t x : nat,
 C_basic t x trois ->
 Verticale (S t) (x + quatre) huit G_Etat ->
 Horizontale (t + neuf) (S x) deux G_Etat.
intros; rewrite plus_neuf; apply H2_Hg.
rewrite (minus_n_n trois); rewrite <- (plus_quatre (S (S (S t))));
 unfold quatre; apply ZCB_Ht1; auto with arith.
elim H0; intros; apply C_ZCB; auto with arith.
rewrite plus_Snm_nSm; rewrite <- (plus_zero (S t)); apply H1; auto with arith.

rewrite plus_Snm_nSm; rewrite <- (plus_un (S t)); apply H1;
 unfold un, huit; auto with arith.

rewrite plus_Snm_nSm; rewrite <- (plus_deux (S t)); apply H1;
 unfold deux, huit; auto with arith.

rewrite plus_Snm_nSm; rewrite <- (plus_trois (S t)); apply H1;
 unfold trois, huit; auto with arith.

rewrite plus_Snm_nSm; apply inclus_vert with (t := S t) (haut := huit);
 auto with arith.
rewrite plus_trois; rewrite plus_huit; auto with arith.

rewrite <- (plus_quatre x); apply inclus_vert with (t := S t) (haut := huit);
 auto with arith.
rewrite plus_deux; rewrite plus_huit; auto with arith.
Qed.

Lemma Hc_DD :
 forall t x cote : nat,
 deux < cote ->
 C_basic t x (S cote) ->
 Verticale (S t) (S (x + S cote)) (S (S (triple cote))) G_Etat ->
 DD (t + S (S (double cote))) (S x) cote.
intros; unfold double; pattern cote at 2 3; rewrite (R3 cote);
 auto with arith.
do 2 rewrite <- plus_S; do 3 rewrite <- plus_Snm_nSm; rewrite plus_assoc;
 apply Ht1_DD with (cote := S cote - trois); auto with arith.
apply R2; auto with arith.

do 3 rewrite <- plus_Snm_nSm; apply ZCB_Ht1; auto with arith.
elim H1; intros; apply C_ZCB; auto with arith.
rewrite <- (plus_zero (S t)); apply H2; auto with arith.

rewrite <- (plus_un (S t)); apply H2; auto with arith.
unfold un; apply le_n_S; auto with arith.

rewrite <- (plus_deux (S t)); apply H2; auto with arith.
unfold deux; do 2 apply le_n_S; apply le_n_triplem;
 apply le_trans with (m := deux); auto with arith.

rewrite <- (plus_trois (S t)); apply H2; auto with arith.
unfold trois; do 2 apply le_n_S; apply le_n_triplem;
 apply le_trans with (m := deux); auto with arith.

apply inclus_vert with (t := S t) (haut := S (S (triple cote)));
 auto with arith.
do 4 rewrite plus_Snm_nSm; apply plus_le_compat_l; do 2 apply le_n_S;
 rewrite <- (plus_trois cote); unfold triple;
 rewrite plus_assoc_reverse; apply plus_le_compat_l;
 apply le_trans with (m := un + deux); auto with arith.

rewrite <- S_pred; auto with arith; apply R2; auto with arith.
Qed.

End C_trapeze.

End trapezes.