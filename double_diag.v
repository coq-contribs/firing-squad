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

Require Export bord.


Section double_diagonale.

Notation rec4 := (Rec4 _ _ _ _ _) (only parsing).

Section definition.

Inductive DD : nat -> nat -> nat -> Prop :=
  | DD_4 : forall t x : nat, quatre_end t x -> DD t x trois
  | DD_5 : forall t x : nat, cinq_end t x -> DD t x quatre
  | DD_A :
      forall t x cote : nat,
      six <= cote ->
      Omod3 cote ->
      A_basic t (x + pred (double (tiers cote))) (S (tiers cote)) ->
      DD (t + S (tiers cote)) x (pred (double (tiers cote))) -> DD t x cote
  | DD_B :
      forall t x cote : nat,
      sept <= cote ->
      Unmod3 cote ->
      B_basic t (x + double (tiers cote)) (S (tiers cote)) ->
      DD (t + S (tiers cote)) x (double (tiers cote)) -> DD t x cote
  | DD_C :
      forall t x cote : nat,
      cinq <= cote ->
      Deuxmod3 cote ->
      C_basic t (x + S (double (tiers cote))) (S (tiers cote)) ->
      DD (t + S (tiers cote)) x (S (double (tiers cote))) -> DD t x cote.

Lemma DD_GG :
 forall t x cote : nat,
 DD t x cote -> G_Etat (t + cote) x /\ G_Etat (S (t + cote)) x.
intros; elim H; intros.
rewrite plus_trois; apply quatre_GG; auto with v62.

rewrite plus_quatre; apply cinq_GG; auto with v62.

generalize H4.
rewrite plus_assoc_reverse; rewrite plus_Snm_nSm; rewrite <- S_pred.
rewrite (plus_comm (tiers cote0) (double (tiers cote0)));
 rewrite plus_deuxtiers_untiers; auto with v62.

apply lt_O_double; apply lt_O_tiers; apply le6_lt2; auto with v62.

generalize H4.
rewrite plus_assoc_reverse; rewrite plus_S.
rewrite (plus_comm (tiers cote0) (double (tiers cote0)));
 rewrite Splus_deuxtiers_untiers; auto with v62.

generalize H4.
rewrite plus_assoc_reverse; rewrite plus_S;
 rewrite <- (plus_n_Sm (tiers cote0)).
rewrite (plus_comm (tiers cote0) (double (tiers cote0)));
 rewrite SSplus_deuxtiers_untiers; auto with v62.
Qed.


End definition.

Section superposition.

Theorem DD_hh :
 forall t x cote : nat,
 DD t x cote ->
 L_Etat (S (S t)) (x + cote) ->
 L_Etat (S (S (S t))) (x + cote) -> DD (S (S t)) x cote.
intros t x cote Hdd; elim Hdd; clear Hdd t x cote; intros.
rewrite (plus_trois x) in H0; rewrite (plus_trois x) in H1; apply DD_4;
 apply quatre_quatre; auto with v62.

rewrite (plus_quatre x) in H0; rewrite (plus_quatre x) in H1; apply DD_5;
 apply cinq_cinq; auto with v62.

apply (Rec4 _ _ _ _ _ (DD_A (S (S t)) x cote)); auto with v62.
clear H0; intros; apply A_A; auto with v62.
rewrite plus_assoc_reverse; rewrite <- plus_Snm_nSm; rewrite <- S_pred.
rewrite plus_deuxtiers_untiers; auto with v62.

apply lt_O_double; apply lt_O_tiers; apply le6_lt2; auto with v62.

rewrite plus_assoc_reverse; rewrite <- plus_Snm_nSm; rewrite <- S_pred.
rewrite plus_deuxtiers_untiers; auto with v62.

apply lt_O_double; apply lt_O_tiers; apply le6_lt2; auto with v62.

intros Ha; elim Ha; clear Ha; intros; apply H3.
elim H7; auto with v62.

elim H8; auto with v62.

apply (Rec4 _ _ _ _ _ (DD_B (S (S t)) x cote)); auto with v62.
intros; apply B_B; auto with v62.
rewrite plus_assoc_reverse; rewrite <- plus_n_Sm;
 rewrite Splus_deuxtiers_untiers; auto with v62.

rewrite plus_assoc_reverse; rewrite <- plus_n_Sm;
 rewrite Splus_deuxtiers_untiers; auto with v62.

intros Hb; elim Hb; clear Hb; intros; apply H3.
elim H7; auto with v62.

elim H8; auto with v62.

apply (Rec4 _ _ _ _ _ (DD_C (S (S t)) x cote)); auto with v62.
intros; apply C_C; auto with v62.
rewrite plus_assoc_reverse; rewrite <- plus_n_Sm; simpl;
 rewrite SSplus_deuxtiers_untiers; auto with v62.

rewrite plus_assoc_reverse; rewrite <- plus_n_Sm; simpl;
 rewrite SSplus_deuxtiers_untiers; auto with v62.

intros Hc; elim Hc; clear Hc; intros; apply H3.
elim H7; auto with v62.

elim H8; auto with v62.
Qed.

Theorem DD_hddollar :
 forall t x cote : nat,
 DD t x cote ->
 L_Etat (S t) (x + S cote) ->
 L_Etat (S (S t)) (x + S cote) -> DD (S t) x (S cote).
intros t x cote Hdd; elim Hdd; clear Hdd t x cote; intros.
apply DD_5; apply quatre_cinq; auto with v62.
generalize H0; rewrite plus_quatre; auto with v62.

generalize H1; rewrite plus_quatre; auto with v62.

apply DD_C; auto with v62.
unfold Deuxmod3; auto with v62.

unfold tiers, double; simpl; elim (cinq_quatre t x);
 auto with v62.

unfold tiers, double; simpl; rewrite plus_deux; apply DD_4;
 elim (cinq_quatre t x); auto with v62.

cut (0 < double (tiers cote)); intros.
apply (Rec4 _ _ _ _ _ (DD_B (S t) x (S cote))); try rewrite <- (tiers_S cote);
 try rewrite (S_pred (double (tiers cote))); auto with v62.
unfold sept; apply le_n_S; auto with v62.

apply Omod3_Unmod3; auto with v62.

intro; rewrite <- plus_n_Sm; apply A_B; auto with v62.
rewrite plus_n_Sm; rewrite <- S_pred; auto with v62.
rewrite plus_assoc_reverse; rewrite <- plus_n_Sm;
 rewrite plus_deuxtiers_untiers; auto with v62.

rewrite plus_n_Sm; rewrite <- S_pred; auto with v62.
rewrite plus_assoc_reverse; rewrite <- plus_n_Sm;
 rewrite plus_deuxtiers_untiers; auto with v62.

intros Hb; elim Hb; clear Hb; intros; apply H3.
elim H8; auto with v62.

elim H9; auto with v62.

apply lt_O_double; apply lt_O_tiers; apply le6_lt2; auto with v62.

apply (Rec4 _ _ _ _ _ (DD_C (S t) x (S cote)));
 try rewrite <- (tiers_SS cote); auto with v62.
unfold cinq; apply le_n_S; apply le_trans with (m := 7);
 auto with v62.

apply Unmod3_Deuxmod3; auto with v62.

intro; rewrite <- plus_n_Sm; apply B_C; auto with v62.
rewrite plus_n_Sm; rewrite plus_assoc_reverse; rewrite <- plus_n_Sm;
 simpl; rewrite Splus_deuxtiers_untiers; auto with v62.

rewrite plus_n_Sm; rewrite plus_assoc_reverse; rewrite <- plus_n_Sm;
 simpl; rewrite Splus_deuxtiers_untiers; auto with v62.

intros Hc; elim Hc; clear Hc; intros; apply H3.
elim H7; auto with v62.

elim H8; auto with v62.

apply (Rec4 _ _ _ _ _ (DD_A (S t) x (S cote)));
 try rewrite <- (tiers_SSS cote); auto with v62.
unfold six; apply le_n_S; auto with v62.

apply Deuxmod3_Omod3; auto with v62.

intro; rewrite double_S; apply C_A; auto with v62.
simpl; rewrite plus_assoc_reverse; rewrite <- plus_Snm_nSm;
 rewrite <- double_S; rewrite tiers_SSS; auto with v62;
 rewrite plus_deuxtiers_untiers; auto with v62.

simpl; rewrite plus_assoc_reverse; rewrite <- plus_Snm_nSm;
 rewrite <- double_S; rewrite tiers_SSS; auto with v62;
 rewrite plus_deuxtiers_untiers; auto with v62.

rewrite double_S; simpl; intros Ha; elim Ha; clear Ha; intros;
 rewrite <- plus_n_Sm; apply DD_hh; auto with v62.
rewrite plus_n_Sm; elim H7; auto with v62.

rewrite plus_n_Sm; elim H8; auto with v62.
Qed.

End superposition.

End double_diagonale.