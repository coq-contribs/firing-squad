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

Require Export geom.

Section constructions.

Section pas_elementaires.

Variable P Q R T : Local_Prop.

Lemma Pas_hh :
 forall t x dt dx : nat,
 loi P Q R T ->
 P (t + S (S dt)) (x + dx) ->
 Q (S t + S dt) (x + S dx) ->
 R (S (S t) + dt) (x + S (S dx)) -> T (S (S t) + S dt) (x + S dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

Lemma Pas_hd :
 forall t x dt dx : nat,
 loi P Q R T ->
 P (t + S dt) (x + dx) ->
 Q (S t + dt) (x + S dx) ->
 R (S t + dt) (S x + S dx) -> T (S t + S dt) (S x + dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

Lemma Pas_dh :
 forall t x dt dx : nat,
 loi P Q R T ->
 P (t + S dt) (x + dx) ->
 Q (t + S dt) (S x + dx) ->
 R (S t + dt) (S x + S dx) -> T (S t + S dt) (S x + dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

Lemma Pas_hddollar :
 forall t x dt dx : nat,
 loi P Q R T ->
 P (t + S dt) (x + dx) ->
 Q (S t + dt) (x + S dx) ->
 R (S t + dt) (x + S (S dx)) -> T (S t + S dt) (x + S dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

Lemma Pas_dhdollar :
 forall t x dt dx : nat,
 loi P Q R T ->
 P (t + S dt) (x + dx) ->
 Q (t + S dt) (x + S dx) ->
 R (S t + dt) (x + S (S dx)) -> T (S t + S dt) (x + S dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

Lemma demi_Pas_h :
 forall t x dt dx : nat,
 loi_droite Q R T ->
 Q (t + S dt) (x + dx) -> R (S t + dt) (x + S dx) -> T (S t + S dt) (x + dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

Lemma demi_Pas_ddollar :
 forall t x dt dx : nat,
 loi_droite Q R T ->
 Q (t + dt) (x + dx) -> R (t + dt) (x + S dx) -> T (t + S dt) (x + dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

Lemma Pas_hb :
 forall t x dt dx : nat,
 loi P Q R T ->
 P (t + S (S dt)) (x + dx) ->
 Q (S t + S dt) (x + S dx) ->
 R (S (S t) + dt) (S x + S dx) -> T (S (S t) + S dt) (S x + dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

Lemma Pas_bb :
 forall t x dt dx : nat,
 loi P Q R T ->
 P (t + S (S dt)) (x + S dx) ->
 Q (S t + S dt) (S x + S dx) ->
 R (S (S t) + dt) (S (S x) + S dx) -> T (S (S t) + S dt) (S (S x) + dx).
intros t x dt dx; repeat rewrite <- plus_n_Sm; simpl; intros;
 auto with arith.
Qed.

End pas_elementaires.

Section superpositions.

Variable t x cote : nat.

Variable P Q R P' Q' R' P'' Q'' R'' : Local_Prop.

Hypothesis PPQP : loi P P' Q'' P''.

Hypothesis PQPQ : loi P Q' P'' Q''.

Hypothesis PQQP : loi P Q' Q'' P''.

Hypothesis PQQQ : loi P Q' Q'' Q''.

Hypothesis PQRQ : loi P Q' R'' Q''.


Hypothesis XPQP : loi_droite P' Q'' P''.


Hypothesis QPPQ : loi Q P' P'' Q''.

Hypothesis QPPR : loi Q P' P'' R''.

Hypothesis QQPQ : loi Q Q' P'' Q''.

Hypothesis QQPR : loi Q Q' P'' R''.

Hypothesis QQQQ : loi Q Q' Q'' Q''.

Hypothesis QQRQ : loi Q Q' R'' Q''.

Hypothesis QRPQ : loi Q R' P'' Q''.


Hypothesis RPPQ : loi R P' P'' Q''.

Hypothesis PQQR : loi P Q' Q'' R''.

Lemma DDD :
 Diag t x cote P Q P ->
 Diag (S t) x cote P' Q' P' ->
 P'' (S (S t)) (x + cote) -> Diag (S (S t)) x cote P'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_Diag; auto with arith.
intros dx; rewrite plus_deux; case dx; intros.
unfold un; apply (Pas_hh P Q' P'' Q''); auto with arith.
rewrite H8; rewrite plus_zero; auto with arith.

rewrite H8; rewrite plus_zero; auto with arith.

unfold un; apply (Pas_hh Q Q' P'' Q''); auto with arith.
rewrite H8; rewrite plus_zero; auto with arith.

intros dt dx; rewrite (plus_S dt); rewrite <- (plus_n_Sm dt); intros;
 apply (Pas_hh Q Q' Q'' Q''); auto with arith.
apply H5; auto with arith.
rewrite (plus_S dt); rewrite <- (plus_n_Sm dt); auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_hh P Q' Q'' Q''); auto with arith.
rewrite H8; rewrite plus_zero; auto with arith.

apply H5; auto with arith.
rewrite plus_un; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H8; rewrite <- (plus_zero x);
 apply (demi_Pas_h P' Q'' P''); auto with arith.
rewrite H8; rewrite plus_zero; auto with arith.
Qed.

Lemma D'DD :
 Diag' t x cote P R Q P ->
 Diag (S t) x cote P' Q' P' ->
 P'' (S (S t)) (x + cote) -> Diag (S (S t)) x cote P'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H4 H; elim H; clear H; intros.
apply Rec_Diag; auto with arith.
intros dx; rewrite plus_deux; case dx; intros.
unfold un; apply (Pas_hh P Q' P'' Q''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

rewrite H9; rewrite plus_zero; auto with arith.

unfold un; apply (Pas_hh Q Q' P'' Q''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

intros dt dx; rewrite (plus_S dt); rewrite <- (plus_n_Sm dt); intros;
 apply (Pas_hh Q Q' Q'' Q''); auto with arith.
apply H6; auto with arith.
rewrite (plus_S dt); rewrite <- (plus_n_Sm dt); auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_hh P Q' Q'' Q''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

apply H6; auto with arith.
rewrite plus_un; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H9; rewrite <- (plus_zero x);
 apply (demi_Pas_h P' Q'' P''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.
Qed.

Lemma D'DD' :
 Diag' t x cote P R Q P ->
 Diag (S t) x cote P' Q' P' ->
 P'' (S (S t)) (x + cote) -> Diag' (S (S t)) x cote P'' R'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H4 H; elim H; clear H; intros.
apply Rec_Diag'; auto with arith.
intros dx; rewrite plus_deux; intros; unfold un;
 apply (Pas_hh Q Q' P'' R''); auto with arith.
apply H3; auto with arith.
do 2 apply lt_S_n; rewrite H9; auto with arith.

rewrite H9; rewrite plus_zero; auto with arith.

intros dx; rewrite plus_trois; case dx; intros.
unfold deux; apply (Pas_hh P Q' R'' Q''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

unfold deux; apply (Pas_hh Q Q' R'' Q''); auto with arith.

intros; apply (Pas_hh Q Q' Q'' Q''); auto with arith.
apply H3; auto with arith.
rewrite plus_Snm_nSm; auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_hh P Q' Q'' Q''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

apply H6; auto with arith.
rewrite plus_un; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H9; rewrite <- (plus_zero x);
 apply (demi_Pas_h P' Q'' P''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.
Qed.

Lemma DD'D :
 Diag t x cote P Q P ->
 Diag' (S t) x cote P' R' Q' P' ->
 P'' (S (S t)) (x + cote) -> Diag (S (S t)) x cote P'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_Diag; auto with arith.
intros dx; rewrite plus_deux; intros; unfold un;
 apply (Pas_hh Q R' P'' Q''); auto with arith.
apply H2; auto with arith.
do 2 apply lt_S_n; rewrite H9; auto with arith.

apply H5; auto with arith.
rewrite plus_un; auto with arith.

rewrite H9; rewrite plus_zero; auto with arith.

intros; apply (Pas_hh Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite plus_Snm_nSm; auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_hh P Q' Q'' Q''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

apply H6; auto with arith.
apply lt_S_n; rewrite H9; auto with arith.

rewrite plus_un; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H9; rewrite <- (plus_zero x);
 apply (demi_Pas_h P' Q'' P''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.
Qed.

Lemma DD_D' :
 deux < cote ->
 Diag t x cote P Q P ->
 Diag (S t) x cote P' Q' P' ->
 P'' (S t) (S x + cote) -> Diag' (S t) (S x) cote P'' R'' Q'' P''.
intros H H0; elim H0; clear H0.
intros H0 H1 H2 H3 H4; elim H4; clear H4; intros.
apply Rec_Diag'; auto with arith.
intros dx; rewrite plus_deux; intros; unfold un;
 apply (Pas_hd Q P' P'' R''); auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

rewrite H9; rewrite plus_zero; auto with arith.

intros dx; rewrite plus_trois; intros; unfold deux;
 apply (Pas_hd Q Q' R'' Q''); auto with arith.

intros; apply (Pas_hd Q Q' Q'' Q''); auto with arith.
apply H6; auto with arith.
rewrite <- plus_Snm_nSm; auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_hd Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite plus_un; auto with arith.

apply H6; auto with arith.
do 2 apply lt_S_n; rewrite H9; auto with arith.

rewrite plus_deux; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H9;
 rewrite <- (plus_zero (S x)); apply (Pas_hd P Q' Q'' P''); 
 auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

apply H6; auto with arith.
apply lt_S_n; rewrite H9; auto with arith.

rewrite plus_un; auto with arith.
Qed.

Lemma D_D'D :
 Diag t x cote P Q P ->
 Diag' t (S x) cote P' R' Q' P' ->
 P'' (S t) (S x + cote) -> Diag (S t) (S x) cote P'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_Diag; auto with arith.
intros dx; rewrite plus_deux; intros; unfold un;
 apply (Pas_dh Q R' P'' Q''); auto with arith.
apply H5; auto with arith.
rewrite plus_un; auto with arith.

rewrite H9; rewrite plus_zero; auto with arith.

intros; apply (Pas_dh Q Q' Q'' Q''); auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_dh Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite plus_un; auto with arith.

apply H6; auto with arith.
apply lt_S_n; rewrite H9; auto with arith.

rewrite plus_un; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H9;
 rewrite <- (plus_zero (S x)); apply (Pas_dh P P' Q'' P''); 
 auto with arith.
rewrite H9; rewrite plus_zero; auto with arith.

rewrite H9; rewrite plus_zero; auto with arith.
Qed.

Lemma DD_Ddollar :
 Diag t x cote P Q P ->
 Diag (S t) x cote P' Q' P' ->
 P'' (S t) (x + S cote) -> Diag (S t) x (S cote) P'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_Diag; auto with v62.
intros dx; rewrite plus_deux; intros H8; injection H8; clear H8; intros;
 unfold un; apply (Pas_hddollar Q P' P'' Q''); 
 auto with v62.
apply H2; auto with v62.
apply lt_S_n; rewrite H8; auto with v62.

rewrite H8; rewrite plus_zero; auto with v62.

rewrite H8; rewrite plus_zero; auto with v62.

intros; apply (Pas_hddollar Q Q' Q'' Q''); auto with v62.
apply H2; auto with v62.
simpl in H10; injection H10; rewrite plus_Snm_nSm; auto with v62.

intros dt; rewrite plus_deux; intros H8; injection H8; clear H8; intros;
 unfold un; apply (Pas_hddollar P Q' Q'' Q''); 
 auto with v62.
rewrite H8; rewrite plus_zero; auto with v62.

apply H5; auto with v62.
apply lt_S_n; rewrite H8; auto with v62.

rewrite plus_un; auto with v62.

intros dt; rewrite plus_un; intros H8; injection H8; clear H8; intros;
 rewrite <- (plus_zero x); apply (demi_Pas_ddollar P' Q'' P''); 
 auto with v62.
rewrite plus_zero; auto with v62.

rewrite <- H8; auto with v62.
Qed.

Lemma D_DDdollar :
 Diag t x cote P Q P ->
 Diag t x (S cote) P' Q' P' ->
 P'' (S t) (x + S cote) -> Diag (S t) x (S cote) P'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_Diag; auto with v62.
intros dx; rewrite plus_deux; intros H8; injection H8; clear H8; intros;
 unfold un; apply (Pas_dhdollar Q Q' P'' Q''); 
 auto with v62.
apply H2; auto with v62.
apply lt_S_n; rewrite H8; auto with v62.

rewrite plus_zero; rewrite H8; auto with v62.

intros; simpl in H10; injection H10; clear H10; rewrite <- plus_Snm_nSm;
 intros H10; apply (Pas_dhdollar Q Q' Q'' Q''); auto with v62.
apply H5; auto with v62.
rewrite <- plus_n_Sm; rewrite H10; auto with v62.

intros dt; rewrite plus_deux; intros H8; injection H8; clear H8; intros;
 unfold un; apply (Pas_dhdollar P Q' Q'' Q''); 
 auto with v62.
rewrite plus_zero; rewrite H8; auto with v62.

apply H5; auto with v62.
rewrite plus_un; rewrite H8; auto with v62.

intros dt; rewrite plus_un; intros H8; injection H8; clear H8; intros;
 rewrite <- (plus_zero x); apply (demi_Pas_h P' Q'' P''); 
 auto with v62.
rewrite plus_zero; auto with v62.

rewrite <- H8; auto with v62.
Qed.

Lemma DD_D :
 deux < cote ->
 Diag t x cote P Q P ->
 Diag (S t) x cote P' Q' P' ->
 P'' (S t) (S x + cote) -> Diag (S t) (S x) cote P'' Q'' P''.
intros Hlt H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_Diag; auto with arith.
intros dx; rewrite plus_deux; intros; unfold un;
 apply (Pas_hd Q P' P'' Q''); auto with arith.
rewrite plus_zero; rewrite H8; auto with arith.

rewrite plus_zero; rewrite H8; auto with arith.

intros; apply (Pas_hd Q Q' Q'' Q''); auto with arith.
apply H5; auto with arith.
rewrite <- plus_Snm_nSm; auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_hd Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite plus_un; auto with arith.

apply H5; auto with arith.
do 2 apply lt_S_n; rewrite H8; auto with arith.

rewrite plus_deux; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H8;
 rewrite <- (plus_zero (S x)); apply (Pas_hd P Q' Q'' P''); 
 auto with arith.
rewrite plus_zero; rewrite H8; auto with arith.

apply H5; auto with arith.
apply lt_S_n; rewrite H8; auto with arith.

rewrite plus_un; auto with arith.
Qed.

Lemma D'D_D :
 Diag' t x cote P R Q P ->
 Diag (S t) x cote P' Q' P' ->
 P'' (S t) (S x + cote) -> Diag (S t) (S x) cote P'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H4 H; elim H; clear H; intros.
apply Rec_Diag; auto with arith.
intros dx; rewrite plus_deux; intros; unfold un;
 apply (Pas_hd R P' P'' Q''); auto with arith.
apply H2; auto with arith.
rewrite plus_un; auto with arith.

rewrite plus_zero; rewrite H9; auto with arith.

rewrite plus_zero; rewrite H9; auto with arith.

intros; apply (Pas_hd Q Q' Q'' Q''); auto with arith.
apply H6; auto with arith.
rewrite <- plus_Snm_nSm; auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_hd Q Q' Q'' Q''); auto with arith.
apply H3; auto with arith.
apply lt_S_n; rewrite H9; auto with arith.

rewrite plus_un; auto with arith.

apply H6; auto with arith.
do 2 apply lt_S_n; rewrite H9; auto with arith.

rewrite plus_deux; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H9;
 rewrite <- (plus_zero (S x)); apply (Pas_hd P Q' Q'' P''); 
 auto with arith.
rewrite plus_zero; rewrite H9; auto with arith.

apply H6; auto with arith.
apply lt_S_n; rewrite H9; auto with arith.

rewrite plus_un; auto with arith.
Qed.

Lemma D_DD :
 Diag t x cote P Q P ->
 Diag t (S x) cote P' Q' P' ->
 P'' (S t) (S x + cote) -> Diag (S t) (S x) cote P'' Q'' P''.
intros H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_Diag; auto with arith.
intros dx; rewrite plus_deux; intros; unfold un;
 apply (Pas_dh Q Q' P'' Q''); auto with arith.
rewrite plus_zero; rewrite H8; auto with arith.

intros; apply (Pas_dh Q Q' Q'' Q''); auto with arith.

intros dt; rewrite plus_deux; intros; unfold un;
 apply (Pas_dh Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite plus_un; auto with arith.

apply H5; auto with arith.
rewrite plus_un; auto with arith.

intros dt; rewrite plus_un; intros; rewrite <- H8;
 rewrite <- (plus_zero (S x)); apply (Pas_dh P P' Q'' P''); 
 auto with arith.
rewrite plus_zero; rewrite H8; auto with arith.

rewrite plus_zero; rewrite H8; auto with arith.
Qed.

Lemma DDdollar_D :
 un < cote ->
 Diag t x (S cote) P Q P ->
 Diag (S t) x (S cote) P' Q' P' ->
 P'' (S (S t)) (S (x + cote)) -> Diag (S (S t)) (S x) cote P'' Q'' R''.
intros Hlt H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_Diag; auto with arith.
intros dx; rewrite plus_deux; intros; unfold un;
 apply (Pas_hb Q Q' P'' Q''); auto with arith.
apply H2; auto with arith.
simpl; rewrite <- H8; auto with arith.

rewrite plus_zero; rewrite H8; auto with arith.

intros; apply (Pas_hb Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite <- H10; auto with arith.

apply H5; auto with arith.
rewrite <- plus_n_Sm; rewrite <- H10; auto with arith.

intros dt; rewrite (plus_deux dt); unfold un; intros;
 apply (Pas_hb Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite plus_un; rewrite <- H8; auto with arith.

apply H5; auto with arith.
rewrite plus_deux; rewrite <- H8; auto with arith.

intros dt; rewrite (plus_un dt); intros; rewrite <- H8;
 rewrite <- (plus_zero (S x)); apply (Pas_hb P Q' Q'' R''); 
 auto with arith.
rewrite H8; rewrite plus_zero; auto with arith.

apply H5; auto with arith.
rewrite plus_un; rewrite <- H8; auto with arith.
Qed.

Lemma DD_d :
 0 < cote ->
 Diag t x (S (S cote)) P Q R ->
 Diag (S t) (S x) (S cote) P' Q' R' ->
 P'' (S (S t)) (S (S (x + cote))) ->
 Semi_Diag (S (S t)) (S (S x)) cote P'' Q''.
intros Hlt H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_SemiDiag; auto with arith.
intros dx; unfold un; intros; simpl in H8;
 apply (Pas_bb Q Q' P'' Q''); auto with arith.
apply H2; auto with arith.
rewrite <- H8; simpl; auto with arith.

rewrite plus_zero; rewrite H8; auto with arith.

intros; apply (Pas_bb Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite <- plus_n_Sm; rewrite <- H9; auto with arith.

apply H5; auto with arith.
rewrite <- plus_n_Sm; rewrite <- H9; auto with arith.
Qed.

Lemma Dd_d :
 0 < cote ->
 Diag t x (S (S cote)) P Q R ->
 Semi_Diag (S t) (S x) (S cote) P' Q' ->
 P'' (S (S t)) (S (S (x + cote))) ->
 Semi_Diag (S (S t)) (S (S x)) cote P'' Q''.
intros Hlt H; elim H; clear H.
intros H0 H1 H2 H3 H; elim H; clear H; intros.
apply Rec_SemiDiag; auto with arith.
intros dx; unfold un; intros; simpl in H7;
 apply (Pas_bb Q Q' P'' Q''); auto with arith.
apply H2; auto with arith.
rewrite <- H7; simpl; auto with arith.

rewrite plus_zero; rewrite H7; auto with arith.

intros; apply (Pas_bb Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite <- plus_n_Sm; rewrite <- H8; auto with arith.

apply H5; auto with arith.
rewrite <- plus_n_Sm; rewrite <- H8; auto with arith.
Qed.

Lemma dd_d :
 0 < cote ->
 Semi_Diag t x (S (S cote)) P Q ->
 Semi_Diag (S t) (S x) (S cote) P' Q' ->
 P'' (S (S t)) (S (S (x + cote))) ->
 Semi_Diag (S (S t)) (S (S x)) cote P'' Q''.
intros Hlt H; elim H; clear H.
intros H0 H1 H2 H; elim H; clear H; intros.
apply Rec_SemiDiag; auto with arith.
intros dx; unfold un; intros; simpl in H6;
 apply (Pas_bb Q Q' P'' Q''); auto with arith.
apply H2; auto with arith.
rewrite <- H6; simpl; auto with arith.

rewrite plus_zero; rewrite H6; auto with arith.

intros; apply (Pas_bb Q Q' Q'' Q''); auto with arith.
apply H2; auto with arith.
rewrite <- plus_n_Sm; rewrite <- H7; auto with arith.

apply H4; auto with arith.
rewrite <- plus_n_Sm; rewrite <- H7; auto with arith.
Qed.

End superpositions.

End constructions.