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

Require Export basic.

Section reflect.

Section UZ.

Inductive UA (t x cote : nat) : Prop :=
    make_UA : un < cote -> Diag t x cote G_Etat A_Etat G_Etat -> UA t x cote.
Inductive UAB (t x cote : nat) : Prop :=
    make_UAB :
      deux < cote ->
      Diag' t x cote G_Etat G_Etat B_Etat G_Etat ->
      Diag (S t) x cote G_Etat A_Etat G_Etat -> UAB t x cote.
Inductive ZCB (t x cote : nat) : Prop :=
    make_ZCB :
      un < cote ->
      Diag t x cote G_Etat C_Etat G_Etat ->
      Diag (S t) x cote G_Etat B_Etat G_Etat -> ZCB t x cote.

End UZ.

Section construction.

Notation rec3 := (Rec3 _ _ _ _) (only parsing).

Variable t x cote : nat.

Lemma B_UA :
 B_basic t x cote -> G_Etat (S t) (S x + cote) -> UA (S t) (S x) cote.
intros H; elim H; clear H; intros; apply make_UA; auto with v62.
apply
 D'D_D
  with
    (P := L_Etat)
    (Q := B_Etat)
    (R := G_Etat)
    (P' := L_Etat)
    (Q' := B_Etat); auto with v62.
unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H3; rewrite H4; rewrite H5; auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H3; rewrite H4; rewrite H5; auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H3; rewrite H4; rewrite H5; auto with v62.
Qed.

Lemma C_UAB :
 deux < cote ->
 C_basic t x cote ->
 G_Etat (S t) (S x + cote) ->
 G_Etat (S (S t)) (S x + cote) -> UAB (S t) (S x) cote.
intros Hlt H; elim H; clear H; intros;
 apply (Rec3 _ _ _ _ (make_UAB (S t) (S x) cote)); 
 auto with v62.
apply DD_D' with (P := L_Etat) (Q := C_Etat) (P' := L_Etat) (Q' := C_Etat);
 auto with v62.
unfold loi, L_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

clear H0; intros H0;
 apply
  D_D'D
   with
     (P := L_Etat)
     (Q := C_Etat)
     (P' := G_Etat)
     (Q' := B_Etat)
     (R' := G_Etat); auto with v62.
unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H4; rewrite H5; rewrite H6; 
 auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H4; rewrite H5; rewrite H6; 
 auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H4; rewrite H5; rewrite H6; 
 auto with v62.
Qed.

Lemma A_ZCB :
 A_basic t x cote ->
 G_Etat (S t) (S x + cote) ->
 G_Etat (S (S t)) (S x + cote) -> ZCB (S t) (S x) cote.
intros H; elim H; clear H; intros;
 apply (Rec3 _ _ _ _ (make_ZCB (S t) (S x) cote)); 
 auto with v62.
apply DD_D with (P := L_Etat) (Q := A_Etat) (P' := L_Etat) (Q' := A_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

clear H0; intros H0;
 apply D_DD with (P := L_Etat) (Q := A_Etat) (P' := G_Etat) (Q' := C_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H4; rewrite H5; rewrite H6; 
 auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H4; rewrite H5; rewrite H6; 
 auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H4; rewrite H5; rewrite H6; 
 auto with v62.
Qed.

Lemma B_ZCB :
 B_basic t x cote ->
 G_Etat (S t) (S x + cote) ->
 G_Etat (S (S t)) (S x + cote) ->
 G_Etat (S (S (S t))) (S x + cote) -> ZCB (S (S t)) (S x) cote.
intros Hb; elim Hb; intros; elim B_UA; auto with v62; clear H0; intros Hlt H0;
 clear Hb Hlt; apply (Rec3 _ _ _ _ (make_ZCB (S (S t)) (S x) cote));
 auto with v62.
apply D_DD with (P := L_Etat) (Q := B_Etat) (P' := G_Etat) (Q' := A_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H5; rewrite H6; rewrite H7; 
 auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H5; rewrite H6; rewrite H7; 
 auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H5; rewrite H6; rewrite H7; 
 auto with v62.

clear H1; intros H1;
 apply DDD with (P := G_Etat) (Q := A_Etat) (P' := G_Etat) (Q' := C_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H5; rewrite H6; rewrite H7; 
 auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H5; rewrite H6; rewrite H7; 
 auto with v62.

unfold loi_droite, B_Etat, G_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H5; rewrite H6; rewrite H7; 
 auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros;
 simpl in |- *; rewrite H5; rewrite H6; rewrite H7; 
 auto with v62.
Qed.

Lemma C_ZCB :
 deux < cote ->
 C_basic t x cote ->
 G_Etat (S t) (S x + cote) ->
 G_Etat (S (S t)) (S x + cote) ->
 G_Etat (S (S (S t))) (S x + cote) ->
 G_Etat (S (S (S (S t)))) (S x + cote) -> ZCB (S (S (S t))) (S x) cote.
intros; elim C_UAB; auto with v62; clear H H0 H1; intros;
 apply (Rec3 _ _ _ _ (make_ZCB (S (S (S t))) (S x) cote)); 
 auto with v62.
apply
 D'DD
  with
    (P := G_Etat)
    (Q := B_Etat)
    (R := G_Etat)
    (P' := G_Etat)
    (Q' := A_Etat); auto with v62.
unfold loi, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H5; rewrite H6; rewrite H7; auto with v62.

unfold loi, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H5; rewrite H6; rewrite H7; auto with v62.

unfold loi_droite, C_Etat, G_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H5; rewrite H6; auto with v62.

unfold loi, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H5; rewrite H6; rewrite H7; auto with v62.

unfold loi, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H5; rewrite H6; rewrite H7; auto with v62.

clear H0; intros H0;
 apply DDD with (P := G_Etat) (Q := A_Etat) (P' := G_Etat) (Q' := C_Etat);
 auto with v62.
unfold loi, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H5; rewrite H6; rewrite H7; auto with v62.

unfold loi, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H5; rewrite H6; rewrite H7; auto with v62.

unfold loi_droite, B_Etat, G_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H5; rewrite H6; auto with v62.

unfold loi, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H5; rewrite H6; rewrite H7; auto with v62.

unfold loi, A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H5; rewrite H6; rewrite H7; auto with v62.
Qed.

End construction.

Section triangle_sup.

Variable t x cote : nat.

Lemma ZCB_GLC :
 deux < cote ->
 ZCB t x cote ->
 Verticale (S (S t)) (x + cote) cote G_Etat ->
 Diag (S t + un) (x + un) (cote - un) G_Etat L_Etat C_Etat.
intros Hlt Hz Hv; elim Hz; clear Hz; elim Hv; clear Hv; intros.
do 2 rewrite plus_un;
 apply
  DDdollar_D with (P := G_Etat) (Q := C_Etat) (P' := G_Etat) (Q' := B_Etat);
 auto with v62.
unfold loi, B_Etat, C_Etat, G_Etat, L_Etat in |- *; intros; simpl in |- *;
 rewrite H3; rewrite H4; rewrite H5; auto with v62.

unfold loi, B_Etat, C_Etat, G_Etat, L_Etat in |- *; intros; simpl in |- *;
 rewrite H3; rewrite H4; rewrite H5; auto with v62.

unfold loi, B_Etat, C_Etat, G_Etat, L_Etat in |- *; intros; simpl in |- *;
 rewrite H3; rewrite H4; rewrite H5; auto with v62.

apply lt_S_n; rewrite Sminus_un; auto with v62.

rewrite Sminus_un; auto with v62.

rewrite Sminus_un; auto with v62.

rewrite <- (plus_zero (S (S t))); rewrite (plus_n_Sm x); rewrite Sminus_un;
 auto with v62.
Qed.

Lemma ZCB_l :
 deux < cote ->
 ZCB t x cote ->
 Verticale (S (S t)) (x + cote) cote G_Etat ->
 Semi_Diag (S t + deux) (x + deux) (cote - deux) G_Etat L_Etat.
intros Hlt Hz Hv; elim Hz; elim Hv; intros.
do 2 rewrite plus_deux;
 apply
  DD_d
   with
     (P := G_Etat)
     (Q := B_Etat)
     (R := G_Etat)
     (P' := G_Etat)
     (Q' := L_Etat)
     (R' := C_Etat).
unfold loi, B_Etat, G_Etat, L_Etat in |- *; intros; simpl in |- *; rewrite H3;
 rewrite H4; rewrite H5; auto with v62.

unfold loi, B_Etat, G_Etat, L_Etat in |- *; intros; simpl in |- *; rewrite H3;
 rewrite H4; rewrite H5; auto with v62.

do 2 apply lt_S_n; rewrite SSminus_deux; auto with v62.

rewrite SSminus_deux; auto with v62.

rewrite <- (plus_un (S t)); rewrite <- (plus_un x); unfold deux in |- *;
 rewrite Sminus_aSb; auto with v62.
apply ZCB_GLC; auto with v62.

rewrite <- (plus_un (S (S t))); do 2 rewrite plus_n_Sm; rewrite SSminus_deux;
 auto with v62.
Qed.

Lemma ZCB_ll :
 trois < cote ->
 ZCB t x cote ->
 Verticale (S (S t)) (x + cote) cote G_Etat ->
 Semi_Diag (S t + trois) (x + trois) (cote - trois) G_Etat L_Etat.
intros Hlt Hz Hv; elim Hv; intros.
do 2 rewrite plus_trois;
 apply
  Dd_d
   with
     (P := G_Etat)
     (Q := L_Etat)
     (R := C_Etat)
     (P' := G_Etat)
     (Q' := L_Etat).
unfold loi, G_Etat, L_Etat in |- *; intros; simpl in |- *; rewrite H0;
 rewrite H1; rewrite H2; auto with v62.

unfold loi, G_Etat, L_Etat in |- *; intros; simpl in |- *; rewrite H0;
 rewrite H1; rewrite H2; auto with v62.

do 3 apply lt_S_n; rewrite SSSminus_trois; auto with v62.

rewrite <- (plus_un (S t)); rewrite <- (plus_un x); unfold trois in |- *;
 do 2 (rewrite Sminus_aSb; auto with v62).
apply ZCB_GLC; auto with v62.

apply lt_trans with (m := trois); auto with v62.

rewrite <- (plus_deux (S t)); rewrite <- (plus_deux x); unfold trois in |- *;
 rewrite Sminus_aSb; auto with v62.
apply ZCB_l; auto with v62.

do 2 rewrite plus_n_Sm; rewrite plus_Snm_nSm;
 rewrite <- (plus_deux (S (S t))); rewrite SSSminus_trois; 
 auto with v62.
apply H; auto with v62.
apply le_trans with (m := trois); auto with v62.
Qed.

Lemma ZCB_lll :
 forall dcote : nat,
 deux <= dcote ->
 dcote < cote ->
 ZCB t x cote ->
 Verticale (S (S t)) (x + cote) cote G_Etat ->
 Semi_Diag (S t + dcote) (x + dcote) (cote - dcote) G_Etat L_Etat.
intros; elim H2; intros.
generalize H0;
 apply
  recur_nSn
   with
     (P := fun dcote : nat =>
           dcote < cote ->
           Semi_Diag (S t + dcote) (x + dcote) (cote - dcote) G_Etat L_Etat)
     (n := deux).
intros; apply ZCB_l; auto with v62.

intros; apply ZCB_ll; auto with v62.

intros; repeat rewrite <- plus_n_Sm;
 apply dd_d with (P := G_Etat) (Q := L_Etat) (P' := G_Etat) (Q' := L_Etat).
unfold loi, G_Etat, L_Etat in |- *; intros; simpl in |- *; rewrite H7;
 rewrite H8; rewrite H9; auto with v62.

unfold loi, G_Etat, L_Etat in |- *; intros; simpl in |- *; rewrite H7;
 rewrite H8; rewrite H9; auto with v62.

apply lt_O_minus; auto with v62.

do 2 (rewrite Sminus_aSb; auto with v62).
apply H4; apply lt_trans with (m := S (S p)); auto with v62.

apply lt_trans with (m := S (S p)); auto with v62.

do 2 rewrite plus_n_Sm; rewrite Sminus_aSb; auto with v62.

rewrite plus_n_Sm; do 3 rewrite <- plus_S; do 2 rewrite plus_n_Sm;
 rewrite plus_assoc_reverse; rewrite le_plus_minus_r; 
 auto with v62.
apply H3; apply le_trans with (m := S (S p)); auto with v62.

auto with v62.
Qed.

Lemma ZCB_Ht1 :
 deux < cote ->
 ZCB t x cote ->
 Verticale (S (S t)) (x + cote) cote G_Etat ->
 Horizontale_t1 (t + S cote) x (cote - trois) G_Etat C_Etat L_Etat.
intros; apply make_horizontale_t1.
rewrite <- plus_Snm_nSm; elim H0; intros; elim H4; auto with v62.

elim ZCB_GLC; auto with v62; intros H2 H3 H4; clear H2 H3 H4.
rewrite plus_assoc_reverse; rewrite (plus_un x); rewrite plus_Snm_nSm;
 rewrite <- le_plus_minus; auto with v62.
apply le_trans with (m := deux); auto with v62.

apply make_horizontale; intros; elim ZCB_lll with (dcote := S (S dx));
 auto with v62; intros.
generalize (H5 (cote - S (S dx)) 0); clear H4 H5; repeat rewrite plus_zero.
rewrite plus_assoc_reverse; rewrite le_plus_minus_r;
 repeat rewrite plus_Snm_nSm; auto with v62.
rewrite <- (SSSminus_trois cote); auto with v62.

unfold deux in |- *; auto with v62.

rewrite <- (SSSminus_trois cote); auto with v62.
Qed.

End triangle_sup.

Section Z_verticale.

Variable t x cote : nat.

Lemma A_Vg :
 A_basic t x cote ->
 G_Etat (S t) (S x + cote) ->
 G_Etat (S (S t)) (S x + cote) -> Verticale (S t + cote) (S x) un G_Etat.
intros; elim (A_ZCB t x cote); auto with v62.
intros; apply vert_un.
elim H3; auto with v62.

elim H4; auto with v62.
Qed.

Lemma B_Vg :
 B_basic t x cote ->
 G_Etat (S t) (S x + cote) ->
 G_Etat (S (S t)) (S x + cote) ->
 G_Etat (S (S (S t))) (S x + cote) ->
 Verticale (S t + cote) (S x) deux G_Etat.
intros; elim (B_ZCB t x cote); auto with v62.
intros; elim (B_UA t x cote); auto with v62.
intros; apply vert_deux.
elim H7; auto with v62.

elim H4; auto with v62.

elim H5; auto with v62.
Qed.

Lemma C_Vg :
 deux < cote ->
 C_basic t x cote ->
 G_Etat (S t) (S x + cote) ->
 G_Etat (S (S t)) (S x + cote) ->
 G_Etat (S (S (S t))) (S x + cote) ->
 G_Etat (S (S (S (S t)))) (S x + cote) ->
 Verticale (S t + cote) (S x) trois G_Etat.
intros; elim (C_ZCB t x cote); auto with v62.
intros; elim (C_UAB t x cote); auto with v62.
intros; apply vert_trois.
elim H9; auto with v62.

elim H10; auto with v62.

elim H6; auto with v62.

elim H7; auto with v62.
Qed.

End Z_verticale.

End reflect.