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

Require Export autom.
Require Export constr.

(*Section briques_de_base. *)

(*Section basic.*)

Definition A_Etat (t x : nat) := Etat t x = A.
Definition B_Etat (t x : nat) := Etat t x = B.
Definition C_Etat (t x : nat) := Etat t x = C.
Definition G_Etat (t x : nat) := Etat t x = G.
Definition L_Etat (t x : nat) := Etat t x = L.
Definition F_Etat (t x : nat) := Etat t x = F.

Inductive A_basic (t x cote : nat) : Prop :=
    make_A_basic :
      deux < cote ->
      Diag t x cote L_Etat A_Etat L_Etat ->
      Diag (S t) x cote L_Etat A_Etat L_Etat -> A_basic t x cote.
Inductive B_basic (t x cote : nat) : Prop :=
    make_B_basic :
      deux < cote ->
      Diag' t x cote L_Etat G_Etat B_Etat L_Etat ->
      Diag (S t) x cote L_Etat B_Etat L_Etat -> B_basic t x cote.
Inductive C_basic (t x cote : nat) : Prop :=
    make_C_basic :
      un < cote ->
      Diag t x cote L_Etat C_Etat L_Etat ->
      Diag (S t) x cote L_Etat C_Etat L_Etat -> C_basic t x cote.

(*End basic.*)

Section construction2.

Notation rec3 := (Rec3 _ _ _ _) (only parsing).

Variable t x cote : nat.

Lemma A_A :
 A_basic t x cote ->
 L_Etat (S (S t)) (x + cote) ->
 L_Etat (S (S (S t))) (x + cote) -> A_basic (S (S t)) x cote.
intros H; elim H; clear H; intros.
apply (Rec3 _ _ _ _ (make_A_basic (S (S t)) x cote)); auto with v62.
apply DDD with (P := L_Etat) (Q := A_Etat) (P' := L_Etat) (Q' := A_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi_droite, L_Etat, A_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H4; rewrite H5; auto with v62.
case (Etat t0 n); auto with v62.

unfold loi, L_Etat, A_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

clear H0; intros H0;
 apply DDD with (P := L_Etat) (Q := A_Etat) (P' := L_Etat) (Q' := A_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi_droite, L_Etat, A_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H4; rewrite H5; auto with v62.
case (Etat t0 n); auto with v62.

unfold loi, L_Etat, A_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.
Qed.

Lemma B_B :
 B_basic t x cote ->
 L_Etat (S (S t)) (x + cote) ->
 L_Etat (S (S (S t))) (x + cote) -> B_basic (S (S t)) x cote.
intros H; elim H; clear H; intros.
apply (Rec3 _ _ _ _ (make_B_basic (S (S t)) x cote)); auto with v62.
apply
 D'DD'
  with
    (P := L_Etat)
    (Q := B_Etat)
    (R := G_Etat)
    (P' := L_Etat)
    (Q' := B_Etat); auto with v62.
unfold loi, L_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi_droite, L_Etat, B_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H4; rewrite H5; auto with v62.
case (Etat t0 n); auto with v62.

unfold loi, L_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

clear H0; intros H0;
 apply
  DD'D
   with
     (P := L_Etat)
     (Q := B_Etat)
     (R' := G_Etat)
     (P' := L_Etat)
     (Q' := B_Etat); auto with v62.
unfold loi, L_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi_droite, L_Etat, B_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H4; rewrite H5; auto with v62.
case (Etat t0 n); auto with v62.

unfold loi, L_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.
Qed.

Lemma C_C :
 C_basic t x cote ->
 L_Etat (S (S t)) (x + cote) ->
 L_Etat (S (S (S t))) (x + cote) -> C_basic (S (S t)) x cote.
intros H; elim H; clear H; intros.
apply (Rec3 _ _ _ _ (make_C_basic (S (S t)) x cote)); auto with v62.
apply DDD with (P := L_Etat) (Q := C_Etat) (P' := L_Etat) (Q' := C_Etat);
 auto with v62.
unfold loi, L_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi_droite, L_Etat, C_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H4; rewrite H5; auto with v62.
case (Etat t0 n); auto with v62.

unfold loi, L_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

clear H0; intros H0;
 apply DDD with (P := L_Etat) (Q := C_Etat) (P' := L_Etat) (Q' := C_Etat);
 auto with v62.
unfold loi, L_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi_droite, L_Etat, C_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H4; rewrite H5; auto with v62.
case (Etat t0 n); auto with v62.

unfold loi, L_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.
Qed.

Lemma A_B :
 A_basic t x cote ->
 L_Etat (S t) (S x + cote) ->
 L_Etat (S (S t)) (S x + cote) -> B_basic (S t) (S x) cote.
intros H; elim H; clear H; intros.
apply (Rec3 _ _ _ _ (make_B_basic (S t) (S x) cote)); auto with v62.
apply DD_D' with (P := L_Etat) (Q := A_Etat) (P' := L_Etat) (Q' := A_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

clear H0; intros H0;
 apply
  D_D'D
   with
     (P := L_Etat)
     (Q := A_Etat)
     (P' := L_Etat)
     (Q' := B_Etat)
     (R' := G_Etat); auto with v62.
unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, B_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.
Qed.

Lemma C_A :
 C_basic t x cote ->
 L_Etat (S t) (x + S cote) ->
 L_Etat (S (S t)) (x + S cote) -> A_basic (S t) x (S cote).
intros H; elim H; clear H; intros.
apply (Rec3 _ _ _ _ (make_A_basic (S t) x (S cote))); auto with v62.
apply
 DD_Ddollar with (P := L_Etat) (Q := C_Etat) (P' := L_Etat) (Q' := C_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi_droite, L_Etat, A_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H4; rewrite H5; auto with v62.
case (Etat t0 n); auto with v62.

unfold loi, L_Etat, A_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

clear H0; intros H0;
 apply
  D_DDdollar with (P := L_Etat) (Q := C_Etat) (P' := L_Etat) (Q' := A_Etat);
 auto with v62.
unfold loi, L_Etat, A_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi_droite, L_Etat, A_Etat in |- *; intros t0 x0; case x0; intros;
 simpl in |- *; rewrite H4; rewrite H5; auto with v62.
case (Etat t0 n); auto with v62.

unfold loi, L_Etat, A_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, A_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.
Qed.

Lemma B_C :
 B_basic t x cote ->
 L_Etat (S t) (S x + cote) ->
 L_Etat (S (S t)) (S x + cote) -> C_basic (S t) (S x) cote.
intros H; elim H; clear H; intros.
apply (Rec3 _ _ _ _ (make_C_basic (S t) (S x) cote)); auto with v62.
apply
 D'D_D
  with
    (P := L_Etat)
    (Q := B_Etat)
    (R := G_Etat)
    (P' := L_Etat)
    (Q' := B_Etat); auto with v62.
unfold loi, L_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; simpl in |- *;
 rewrite H4; rewrite H5; rewrite H6; auto with v62.

clear H0; intros H0;
 apply D_DD with (P := L_Etat) (Q := B_Etat) (P' := L_Etat) (Q' := C_Etat);
 auto with v62.
unfold loi, L_Etat, B_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.

unfold loi, L_Etat, B_Etat, C_Etat in |- *; intros; simpl in |- *; rewrite H4;
 rewrite H5; rewrite H6; auto with v62.
Qed.

End construction2.

Section sommet.

Lemma GA_G : forall t x : nat, G_Etat t x -> A_Etat t (S x) -> G_Etat (S t) x.
unfold A_Etat, G_Etat in |- *; intros t x; case x; intros.
rewrite demi_pas; rewrite H; rewrite H0; auto with v62.

rewrite un_pas; rewrite H; rewrite H0; auto with v62.
Qed.

Lemma GB_G : forall t x : nat, G_Etat t x -> B_Etat t (S x) -> G_Etat (S t) x.
unfold B_Etat, G_Etat in |- *; intros t x; case x; intros.
rewrite demi_pas; rewrite H; rewrite H0; auto with v62.

rewrite un_pas; rewrite H; rewrite H0; auto with v62.
Qed.

Lemma GC_G : forall t x : nat, G_Etat t x -> C_Etat t (S x) -> G_Etat (S t) x.
unfold C_Etat, G_Etat in |- *; intros t x; case x; intros.
rewrite demi_pas; rewrite H; rewrite H0; auto with v62.

rewrite un_pas; rewrite H; rewrite H0; auto with v62.
Qed.

Lemma GA_dollarC :
 forall t x : nat, G_Etat t x -> A_Etat t (S x) -> C_Etat (S t) (S x).
unfold A_Etat, C_Etat, G_Etat in |- *; intros; rewrite un_pas; rewrite H;
 rewrite H0; auto with v62.
Qed.

Lemma GBA_dollarC :
 forall t x : nat,
 G_Etat t x -> B_Etat t (S x) -> A_Etat t (S (S x)) -> C_Etat (S t) (S x).
unfold A_Etat, B_Etat, C_Etat, G_Etat in |- *; intros; rewrite un_pas;
 rewrite H; rewrite H0; rewrite H1; auto with v62.
Qed.

Lemma GBG_dollarG :
 forall t x : nat,
 G_Etat t x -> B_Etat t (S x) -> G_Etat t (S (S x)) -> G_Etat (S t) (S x).
unfold B_Etat, G_Etat in |- *; intros; rewrite un_pas; rewrite H; rewrite H0;
 rewrite H1; auto with v62.
Qed.

Lemma GBC_dollarB :
 forall t x : nat,
 G_Etat t x -> B_Etat t (S x) -> C_Etat t (S (S x)) -> B_Etat (S t) (S x).
unfold B_Etat, C_Etat, G_Etat in |- *; intros; rewrite un_pas; rewrite H;
 rewrite H0; rewrite H1; auto with v62.
Qed.

Lemma GC_dollarB :
 forall t x : nat, G_Etat t x -> C_Etat t (S x) -> B_Etat (S t) (S x).
unfold B_Etat, C_Etat, G_Etat in |- *; intros; rewrite un_pas; rewrite H;
 rewrite H0; auto with v62.
Qed.

End sommet.

(*End briques_de_base. *)


