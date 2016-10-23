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

Require Import sommet.

Section finale.

Remark N_un : autom.N = S (pred autom.N).
apply S_pred.
apply lt_trans with (m := deux); auto with arith.
apply necessaire.
Qed.

Remark N_deux : autom.N = S (S (pred (pred autom.N))).
rewrite <- S_pred.
apply N_un.

apply lt_S_n; rewrite <- N_un.
apply lt_trans with (m := deux); auto with arith.
apply necessaire.
Qed.

Remark N_trois : autom.N = S (S (S (pred (pred (pred autom.N))))).
rewrite <- S_pred.
apply N_deux.

do 2 apply lt_S_n; rewrite <- N_deux.
apply necessaire.
Qed.

Remark R1 : S (pred (pred autom.N)) + autom.N <= un + pred (double autom.N).
rewrite <- S_pred; unfold un, double; simpl.
rewrite <- S_pred.
apply plus_le_compat; auto with arith.

rewrite N_un; simpl; auto with arith.

rewrite N_deux; simpl; auto with arith.
Qed.

Lemma base1 : Horizontale_t0 0 0 (pred autom.N) G_Etat L_Etat.
apply make_horizontale_t0.
unfold G_Etat; apply G00.

apply make_horizontale; intros; simpl.
unfold L_Etat; apply base_L; auto with arith.
rewrite N_un; apply lt_n_S; auto with arith.
Qed.

Lemma diagonale : DD (pred (pred autom.N)) 0 autom.N.
rewrite N_un; simpl.
replace (pred (pred autom.N)) with (0 + pred (pred autom.N)); auto with arith.
apply Ht0_DDf.
rewrite N_trois; simpl; unfold un; auto with arith.

apply base1.
Qed.

Lemma base2 :
 Horizontale_t1 0 (S autom.N) (pred autom.N) G_Etat C_Etat L_Etat.
apply make_horizontale_t1.
unfold G_Etat; apply G0N.

unfold C_Etat; apply C0N1.

apply make_horizontale; intros; simpl.
unfold L_Etat; apply basedollar_L; auto with arith.
Qed.

Lemma vert_droite : Verticale un (S autom.N) (pred (double autom.N)) G_Etat.
pattern autom.N at 2; rewrite N_un; rewrite double_S; simpl.
unfold un; apply Ht1_VV.
apply base2.
Qed.

Remark GN1 : G_Etat (pred (double autom.N)) (S autom.N).
generalize vert_droite; rewrite N_un; rewrite double_S; simpl; intros.
elim H; unfold un; simpl; intros.
apply H0; auto with arith.
Qed.

Lemma sommet_1 : Horizontale (pred (double autom.N)) 0 autom.N G_Etat.
unfold double; pattern autom.N at 1; rewrite N_deux;
 simpl; apply DD_Hg.
apply diagonale.

simpl;
 apply inclus_vert with (t := un) (haut := pred (double autom.N)).
apply le_S_n; rewrite <- N_deux; unfold un; apply lt_le_weak;
 apply necessaire.

apply R1.

apply vert_droite.
Qed.

Theorem firing_squad : Horizontale (double autom.N) 0 autom.N F_Etat.
rewrite N_un; unfold double; simpl; apply Hg_Hf;
 auto with arith.
rewrite plus_pred.
rewrite <- N_un; apply sommet_1.

apply lt_trans with (m := deux); auto with arith.
apply necessaire.

rewrite plus_pred.
rewrite <- N_un; apply GN1.

apply lt_trans with (m := deux); auto with arith.
apply necessaire.
Qed.

End finale. 