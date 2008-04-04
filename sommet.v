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

Require Export trapeze.

Section sommet.

Section cas_particuliers.

Section quatre.

Variable t x : nat.

Hypothesis He : quatre_end t x.

Hypothesis Hv : Verticale (S t) (x + quatre) trois G_Etat.

Lemma C23 : C_Etat (S (S t)) (S (S (S x))).
elim He; unfold L_Etat in |- *; elim Hv; intros.
elim H2; unfold A_Etat in |- *; intros.
generalize (H 0); rewrite plus_zero; rewrite plus_quatre;
 unfold trois, G_Etat in |- *; intros.
unfold C_Etat in |- *; rewrite un_pas; rewrite H1; rewrite H3; rewrite H6;
 auto with v62.
Qed.

Lemma G32 : G_Etat (S (S (S t))) (S (S x)).
apply GC_G.
elim He; intros; elim H1; auto with v62.

apply C23.
Qed.

Remark quatre_B33 : B_Etat (S (S (S t))) (S (S (S x))).
apply GC_dollarB.
elim He; intros; elim H1; auto with v62.

apply C23.
Qed.

Lemma quatre_Hg : Horizontale (t + quatre) x trois G_Etat.
rewrite plus_quatre; apply hor_trois.
elim He; intros; elim H1; intros; elim H4; intros; elim H7; auto with v62.

apply GBG_dollarG.
elim He; intros.
elim H1; intros.
elim H4; intros.
elim H7; auto with v62.

elim He; intros.
elim H1; intros.
elim H4; auto with v62.

apply G32.

apply GB_G.
apply G32.

apply quatre_B33.

apply GBG_dollarG.
apply G32.

apply quatre_B33.

elim Hv; rewrite plus_quatre; intros.
generalize (H deux); rewrite plus_deux; intros; auto with v62.
Qed.

End quatre.

Section cinq.

Variable t x : nat.

Hypothesis He : cinq_end t x.

Hypothesis Hv : Verticale (S t) (x + cinq) quatre G_Etat.

Lemma A24 : A_Etat (S (S t)) (S (S (S (S x)))).
elim He; unfold L_Etat, G_Etat in |- *; elim Hv; intros.
generalize (H 0); rewrite plus_zero; rewrite plus_cinq;
 unfold quatre, G_Etat in |- *; intros.
unfold A_Etat in |- *; rewrite un_pas; rewrite H1; rewrite H2; rewrite H5;
 auto with v62.
Qed.

Lemma B33 : B_Etat (S (S (S t))) (S (S (S x))).
elim He; unfold B_Etat in |- *; intros; elim H3; unfold A_Etat in |- *;
 intros.
generalize A24; unfold A_Etat in |- *; intros.
rewrite un_pas; rewrite H2; rewrite H4; rewrite H7; auto with v62.
Qed.

Lemma C34 : C_Etat (S (S (S t))) (S (S (S (S x)))).
generalize A24; elim He; unfold B_Etat, A_Etat in |- *; elim Hv; intros.
generalize (H un); rewrite plus_un; rewrite plus_cinq;
 unfold un, quatre, G_Etat in |- *; intros.
unfold C_Etat in |- *; rewrite un_pas; rewrite H3; rewrite H5; rewrite H6;
 auto with v62.
Qed.

Lemma G42 : G_Etat (S (S (S (S t)))) (S (S x)).
apply GB_G.
elim He; intros; elim H3; auto with v62.

apply B33.
Qed.

Lemma B43 : B_Etat (S (S (S (S t)))) (S (S (S x))).
apply GBC_dollarB.
elim He; intros; elim H3; auto with v62.

apply B33.

apply C34.
Qed.

Lemma G44 : G_Etat (S (S (S (S t)))) (S (S (S (S x)))).
generalize B33; generalize C34; elim Hv;
 unfold B_Etat, C_Etat, G_Etat in |- *; intros.
generalize (H deux); rewrite plus_deux; rewrite plus_cinq;
 unfold deux, quatre in |- *; intros.
rewrite un_pas; rewrite H0; rewrite H1; rewrite H2; auto with v62.
Qed.

Lemma cinq_Hg : Horizontale (t + cinq) x quatre G_Etat.
rewrite plus_cinq; apply hor_quatre.
elim He; intros; elim H3; intros; elim H6; intros; elim H9; auto with v62.

apply GBG_dollarG.
elim He; intros; elim H3; intros; elim H6; intros; elim H9; auto with v62.

elim He; intros; elim H3; intros; elim H6; auto with v62.

apply G42.

apply GB_G.
apply G42.

apply B43.

apply GBG_dollarG.
apply G42.

apply B43.

apply G44.

generalize B43; generalize G44; elim Hv; unfold B_Etat, G_Etat in |- *;
 intros.
generalize (H trois); rewrite plus_trois; rewrite plus_cinq;
 unfold trois, quatre in |- *; intros.
rewrite un_pas; rewrite H0; rewrite H1; rewrite H2; auto with v62.
Qed.

End cinq.

End cas_particuliers.

Section cas_general.

Lemma R1 : forall n : nat, six <= n -> pred (double (tiers n)) < n.
intros; apply lt_le_trans with (m := double (tiers n)).
apply lt_pred_n_n; apply lt_O_deuxtiers; apply le_trans with (m := six);
 unfold trois, six in |- *; auto with v62.

apply le_deuxtiers_un.
Qed.

Lemma R2 :
 forall x cote : nat,
 six <= cote ->
 Omod3 cote -> x + pred (double (tiers cote)) + S (tiers cote) = x + cote.
intros; rewrite plus_assoc_reverse; rewrite <- plus_Snm_nSm;
 rewrite <- S_pred.
rewrite plus_deuxtiers_untiers; auto with v62.

apply lt_O_deuxtiers; apply le_trans with (m := six);
 unfold trois, six in |- *; auto with v62.
Qed.

Lemma R4 :
 forall m x : nat, x + double (S m) + S (S m) = x + S (S m + S m + S m).
intros; rewrite plus_assoc_reverse; rewrite plus_n_Sm; auto with v62.
Qed.

Lemma R5 :
 forall x cote : nat,
 Deuxmod3 cote -> x + S (double (tiers cote)) + S (tiers cote) = x + cote.
intros; rewrite plus_assoc_reverse; rewrite <- plus_n_Sm; rewrite plus_S;
 rewrite SSplus_deuxtiers_untiers; auto with v62.
Qed.

Lemma R6 :
 forall m0 x : nat,
 x + S (double (S (S m0))) + S (S (S m0)) =
 x + S (S (S (S m0) + S (S m0) + S (S m0))).
intros; rewrite plus_assoc_reverse; rewrite plus_n_Sm; auto with v62.
Qed.

Lemma R53 : forall n : nat, cinq <= n -> trois <= n.
intros; apply le_trans with (m := cinq); unfold trois, cinq in |- *;
 auto with v62.
Qed.

Lemma R76 : forall n : nat, sept <= n -> six <= n.
intros; apply le_trans with (m := sept); unfold six, sept in |- *;
 auto with v62.
Qed.

Theorem DD_Hg :
 forall t x cote : nat,
 DD t x cote ->
 Verticale (S t) (S (x + cote)) cote G_Etat ->
 Horizontale (S (t + cote)) x cote G_Etat.
intros;
 apply
  (recur2
     (fun cote : nat =>
      forall t x : nat,
      DD t x cote ->
      Verticale (S t) (S (x + cote)) cote G_Etat ->
      Horizontale (S (t + cote)) x cote G_Etat)); auto with v62.
clear H0 H t x cote; intros cote Hr t x Hdd; generalize Hr; case Hdd;
 clear Hr Hdd t x cote; intros.
rewrite plus_n_Sm; rewrite (plus_n_Sm x trois) in H0; apply quatre_Hg;
 auto with v62.

rewrite plus_n_Sm; rewrite (plus_n_Sm x quatre) in H0; apply cinq_Hg;
 auto with v62.

rewrite <- (plus_deuxtiers_untiers cote); auto with v62;
 rewrite (S_pred (double (tiers cote))).
apply hh_hor.
rewrite plus_S; rewrite (plus_comm (pred (double (tiers cote))) (tiers cote));
 rewrite <- (plus_S (tiers cote)); rewrite plus_assoc; 
 apply Hr; auto with v62.
apply R1; auto with v62.

apply Ha_Vg; auto with v62.
rewrite R2; auto with v62.
unfold triple in |- *; rewrite triple_tiers; auto with v62.

generalize (le_tiers_six cote H); intros.
generalize H3; pattern cote at 1 2 in |- *; rewrite <- (triple_tiers cote).
generalize H1; inversion H4.
unfold double, deux in |- *; simpl in |- *.
intros; rewrite (plus_n_Sm t); rewrite <- (plus_n_Sm x); apply Ha3_Hg;
 auto with v62.
rewrite plus_trois; rewrite plus_quatre; rewrite <- (plus_six x);
 auto with v62.

intros; rewrite plus_assoc; apply Hr.
rewrite H5; apply lt_tiersn_n; apply lt_trans with (m := 5); auto with v62.

rewrite <- (plus_n_Sm x); rewrite <- S_pred.
apply Ha_DD; auto with v62.
rewrite plus_assoc_reverse; rewrite <- plus_Snm_nSm;
 unfold double, triple in |- *; rewrite <- S_pred; 
 auto with v62.

unfold double in |- *; auto with v62.

rewrite plus_assoc_reverse; unfold double in |- *; rewrite <- S_pred;
 auto with v62.
apply inclus_vert with (t := S t) (haut := S m + S m + S m); auto with v62.
rewrite <- plus_S; repeat rewrite plus_assoc_reverse; auto with v62.

auto with v62.

apply lt_O_deuxtiers; apply le_trans with (m := six);
 unfold trois, six in |- *; auto with v62.

rewrite <- (Splus_deuxtiers_untiers cote); auto with v62.
do 2 rewrite <- plus_S; apply hh_hor.
rewrite plus_S; rewrite (plus_comm (S (double (tiers cote))) (tiers cote));
 rewrite <- plus_Snm_nSm; rewrite plus_assoc; apply Hr; 
 auto with v62.
apply lt_deuxtiersn_n; apply lt_le_trans with (m := sept);
 unfold sept in |- *; auto with v62.

apply Hb_Vg; auto with v62.
rewrite plus_assoc_reverse; rewrite <- plus_n_Sm;
 rewrite Splus_deuxtiers_untiers; auto with v62.
unfold triple in |- *; rewrite Striple_tiers; auto with v62.

generalize (R76 cote H); intros.
generalize (le_tiers_six cote H4); intros.
generalize H3; pattern cote at 1 2 in |- *; rewrite <- (Striple_tiers cote);
 auto with v62.
generalize H1; inversion H5.
unfold double, deux in |- *; rewrite plus_quatre; rewrite plus_sept;
 simpl in |- *; intros.
rewrite plus_n_Sm; rewrite plus_cinq; apply Hb3_Hg; auto with v62.
rewrite plus_quatre; auto with v62.

intros; rewrite plus_S; rewrite plus_assoc; apply Hr.
rewrite H6; apply lt_tiersn_n; apply lt_le_trans with (m := six);
 unfold six in |- *; auto with v62.

rewrite <- (plus_n_Sm x); apply Hb_DD; auto with v62.
rewrite R4; unfold triple in |- *; auto with v62.

rewrite <- (plus_n_Sm x); rewrite plus_Snm_nSm; rewrite R4;
 apply inclus_vert with (t := S t) (haut := S (S m + S m + S m));
 auto with v62.
unfold double in |- *; simpl in |- *; rewrite plus_assoc_reverse;
 simpl in |- *; auto with v62.

rewrite <- (SSplus_deuxtiers_untiers cote); auto with v62.
do 3 rewrite <- plus_S; apply hh_hor.
rewrite plus_S; rewrite (plus_Snm_nSm (S (double (tiers cote))));
 rewrite (plus_comm (S (double (tiers cote))) (S (tiers cote)));
 rewrite plus_assoc; apply Hr; auto with v62.
apply lt_Sdeuxtiersn_n; auto with v62.

apply Hc_Vg; auto with v62.
rewrite R5; auto with v62.
unfold triple in |- *; rewrite SStriple_tiers; auto with v62.

generalize (R53 cote H); intros.
generalize (le_tiers_trois cote H4); intros.
generalize H3; pattern cote at 1 2 in |- *; rewrite <- (SStriple_tiers cote);
 auto with v62.
generalize H1; inversion H5.
unfold double, un in |- *; simpl in |- *; rewrite plus_trois;
 rewrite plus_cinq; intros.
rewrite plus_n_Sm; rewrite plus_quatre; apply Hc2_Hg; auto with v62.
rewrite plus_trois; auto with v62.

inversion H7.
unfold double, un in |- *; simpl in |- *; rewrite plus_cinq;
 rewrite plus_huit; intros.
rewrite plus_n_Sm; rewrite plus_six; apply Hc3_Hg; auto with v62.
rewrite plus_quatre; auto with v62.

intros; rewrite plus_S; rewrite plus_assoc; apply Hr.
rewrite H9; rewrite H6; apply lt_tiersn_n;
 apply lt_le_trans with (m := trois); unfold trois in |- *; 
 auto with v62.

rewrite <- (plus_n_Sm x); apply Hc_DD; auto with v62.
unfold deux in |- *; auto with v62.

rewrite R6; unfold triple in |- *; auto with v62.

rewrite <- (plus_n_Sm x); rewrite plus_Snm_nSm; rewrite R6.
apply
 inclus_vert with (t := S t) (haut := S (S (S (S m0) + S (S m0) + S (S m0))));
 auto with v62.
unfold double in |- *; simpl in |- *; rewrite plus_assoc_reverse;
 simpl in |- *; auto with v62.
Qed.

End cas_general.

Section superposition_h.

Lemma Hg_Hf :
 forall t long : nat,
 0 < long ->
 Horizontale t 0 long G_Etat ->
 G_Etat t (S long) -> Horizontale (S t) 0 long F_Etat.
intros; apply make_horizontale.
intros dx; case dx.
intros; unfold F_Etat in |- *; simpl in |- *.
elim H0; unfold G_Etat in |- *; intros.
generalize (H3 0); simpl in |- *; intros.
generalize (H3 1); simpl in |- *; intros.
rewrite H4; try rewrite H5; auto with v62.

intros; case (le_lt_eq_dec (S n) long); auto with v62.
intros; unfold F_Etat in |- *; simpl in |- *.
elim H0; unfold G_Etat in |- *; intros.
generalize (H3 n); simpl in |- *; intros.
generalize (H3 (S n)); simpl in |- *; intros.
generalize (H3 (S (S n))); simpl in |- *; intros.
rewrite H4; try rewrite H5; try rewrite H6; auto with v62.

intros; unfold F_Etat in |- *; simpl in |- *.
elim H0; unfold G_Etat in |- *; intros.
generalize (H3 n); simpl in |- *; intros.
generalize (H3 (S n)); simpl in |- *; intros.
rewrite <- e in H1; unfold G_Etat in H1.
rewrite H4; auto with v62. 
rewrite H5; auto with v62.
rewrite H1; auto with v62.
Qed.

End superposition_h.

End sommet.