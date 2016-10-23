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

Section bord_gauche.

Notation rec2 := (Rec2 _ _ _) (only parsing).

Notation rec3 := (Rec3 _ _ _ _) (only parsing).

Notation rec5 := (Rec5' _ _ _ _ _ _) (only parsing).

Section n_end.

Inductive un_end (t x : nat) : Prop :=
    make_un_end : G_Etat t x -> G_Etat (S t) x -> un_end t x.

Inductive deux_end (t x : nat) : Prop :=
    make_deux_end :
      C_Etat t (S x) -> B_Etat (S t) (S x) -> un_end (S t) x -> deux_end t x.

Inductive trois_end (t x : nat) : Prop :=
    make_trois_end :
      A_Etat t (S (S x)) ->
      G_Etat (S t) (S (S x)) -> deux_end (S t) x -> trois_end t x.

Inductive quatre_end (t x : nat) : Prop :=
    make_quatre_end :
      L_Etat t (S (S (S x))) ->
      L_Etat (S t) (S (S (S x))) -> trois_end (S t) x -> quatre_end t x.

Inductive cinq_end (t x : nat) : Prop :=
    make_cinq_end :
      L_Etat t (S (S (S (S x)))) ->
      L_Etat (S t) (S (S (S (S x)))) ->
      G_Etat (S t) (S (S (S x))) ->
      B_Etat (S (S t)) (S (S (S x))) -> trois_end (S (S t)) x -> cinq_end t x.

End n_end.

Section end_GG.

Lemma un_GG : forall t x : nat, un_end t x -> G_Etat t x /\ G_Etat (S t) x.
intros; elim H; auto with arith.
Qed.

Lemma deux_GG :
 forall t x : nat, deux_end t x -> G_Etat (S t) x /\ G_Etat (S (S t)) x.
intros; apply un_GG; elim H; auto with arith.
Qed.

Lemma trois_GG :
 forall t x : nat,
 trois_end t x -> G_Etat (S (S t)) x /\ G_Etat (S (S (S t))) x.
intros; apply deux_GG; elim H; auto with arith.
Qed.

Lemma quatre_GG :
 forall t x : nat,
 quatre_end t x -> G_Etat (S (S (S t))) x /\ G_Etat (S (S (S (S t)))) x.
intros; apply trois_GG; elim H; auto with arith.
Qed.

Lemma cinq_GG :
 forall t x : nat,
 cinq_end t x -> G_Etat (S (S (S (S t)))) x /\ G_Etat (S (S (S (S (S t))))) x.
intros; apply trois_GG; elim H; auto with arith.
Qed.


End end_GG.

Section premier_end.

Lemma un_deux :
 forall t x : nat,
 un_end t x ->
 C_Etat (S t) (S x) -> B_Etat (S (S t)) (S x) -> deux_end (S t) x.
intros t x H; elim H; clear H; intros; apply make_deux_end; auto with arith.
apply (Rec2 _ _ _ (make_un_end (S (S t)) x)).
apply GC_G; auto with arith.

intros; apply GB_G; auto with arith.
Qed.

Lemma deux_trois :
 forall t x : nat,
 deux_end t x ->
 A_Etat (S t) (S (S x)) -> G_Etat (S (S t)) (S (S x)) -> trois_end (S t) x.
intros t x H; elim H; clear H; intros; apply make_trois_end; auto with arith.
apply (Rec3 _ _ _ _ (un_deux (S t) x)); auto with arith; elim H1; clear H1;
 intros.
apply (GBA_dollarC (S t) x); auto with arith.

apply (GC_dollarB (S (S t)) x); auto with arith.
Qed.

Lemma deux_quatre :
 forall t x : nat,
 deux_end t x ->
 L_Etat t (S (S x)) ->
 L_Etat t (S (S (S x))) -> L_Etat (S t) (S (S (S x))) -> quatre_end t x.
intros t x H; elim H; unfold B_Etat, C_Etat, L_Etat; intros;
 apply make_quatre_end; auto with arith.
apply (Rec3 _ _ _ _ (deux_trois t x)); auto with arith.
unfold A_Etat; rewrite un_pas; rewrite H0; rewrite H3; rewrite H4;
 auto with arith.

unfold A_Etat, G_Etat; intros; rewrite un_pas; rewrite H1; rewrite H6;
 rewrite H5; auto with arith.
Qed.

Lemma trois_quatre :
 forall t x : nat,
 trois_end t x ->
 L_Etat (S t) (S (S (S x))) ->
 L_Etat (S (S t)) (S (S (S x))) -> trois_end (S (S t)) x.
intros t x H; elim H; clear H; unfold A_Etat, L_Etat, G_Etat; intros.
apply (Rec3 _ _ _ _ (deux_trois (S t) x)); auto with arith; elim H1; clear H1;
 unfold A_Etat, B_Etat, C_Etat, G_Etat; intros; 
 rewrite un_pas.
rewrite H0; rewrite H1; rewrite H2; auto with arith.

rewrite H3; rewrite H4; rewrite H6; auto with arith.
Qed.

Lemma trois_cinq :
 forall t x : nat,
 trois_end t x ->
 G_Etat (S t) (S (S (S x))) ->
 B_Etat (S (S t)) (S (S (S x))) -> trois_end (S (S t)) x.
intros t x H; elim H; clear H; unfold A_Etat, B_Etat, G_Etat; intros.
apply (Rec3 _ _ _ _ (deux_trois (S t) x)); auto with arith; elim H1; clear H1;
 unfold A_Etat, B_Etat, C_Etat, G_Etat, un, deux; 
 intros; rewrite un_pas.
rewrite H0; rewrite H1; rewrite H2; auto with arith.

rewrite H3; rewrite H4; rewrite H6; auto with arith.
Qed.

End premier_end.

Section idem_end.

Lemma quatre_quatre :
 forall t x : nat,
 quatre_end t x ->
 L_Etat (S (S t)) (S (S (S x))) ->
 L_Etat (S (S (S t))) (S (S (S x))) -> quatre_end (S (S t)) x.
intros t x H; elim H; clear H; intros; apply make_quatre_end; auto with arith.
apply trois_quatre; auto with arith.
Qed.

Lemma cinq_cinq :
 forall t x : nat,
 cinq_end t x ->
 L_Etat (S (S t)) (S (S (S (S x)))) ->
 L_Etat (S (S (S t))) (S (S (S (S x)))) -> cinq_end (S (S t)) x.
intros t x H; elim H; clear H; unfold L_Etat, B_Etat, G_Etat; intros.
apply (Rec5' _ _ _ _ _ _ (make_cinq_end (S (S t)) x));
 unfold B_Etat, G_Etat, L_Etat; auto with arith.
elim H3; clear H H0 H1 H3; unfold A_Etat, G_Etat; intros;
 rewrite un_pas.
rewrite H; rewrite H2; rewrite H4; auto with arith.

elim H3; clear H H0 H1 H3; unfold G_Etat; intros; rewrite un_pas.
rewrite H0; rewrite H6; rewrite H5; auto with arith.

intros; apply trois_cinq; auto with arith.
Qed.

End idem_end.

Section suivant_end.

Lemma quatre_cinq :
 forall t x : nat,
 quatre_end t x ->
 L_Etat (S t) (S (S (S (S x)))) ->
 L_Etat (S (S t)) (S (S (S (S x)))) -> cinq_end (S t) x.
intros t x H; elim H; clear H; unfold L_Etat, B_Etat, G_Etat; intros.
apply (Rec5' _ _ _ _ _ _ (make_cinq_end (S t) x)).
unfold L_Etat; auto with arith.

unfold L_Etat; auto with arith.

elim H1; clear H H1; unfold A_Etat, L_Etat, G_Etat; intros;
 rewrite un_pas.
rewrite H; rewrite H0; rewrite H2; auto with arith.

elim H1; clear H H1; unfold B_Etat, L_Etat, G_Etat; intros;
 rewrite un_pas.
rewrite H1; rewrite H6; rewrite H3; auto with arith.

intros; apply trois_cinq; auto with arith.
Qed.

Lemma cinq_quatre :
 forall t x : nat,
 cinq_end t x ->
 L_Etat (S t) (x + cinq) ->
 L_Etat (S (S t)) (x + cinq) ->
 C_basic (S t) (x + trois) deux /\ quatre_end (S (S (S t))) x.
intros t x H; elim H; clear H; unfold L_Etat, B_Etat, G_Etat;
 rewrite plus_trois; rewrite plus_cinq; intros; apply and_impl.
elim H3; clear H H3; unfold A_Etat, G_Etat; intros;
 apply (Rec3 _ _ _ _ (make_C_basic (S t) (S (S (S x))) deux)).
auto with arith.

apply (Rec3 _ _ _ _ (deux_Diag L_Etat C_Etat (S t) (S (S (S x))))).
unfold L_Etat; auto with arith.

unfold C_Etat; rewrite un_pas.
rewrite H1; rewrite H0; rewrite H4; auto with arith.

elim H6; clear H6; unfold A_Etat, L_Etat, C_Etat; intros;
 rewrite un_pas.
rewrite H; rewrite H2; rewrite H9; auto with arith.

clear H H0 H1 H4; intros H;
 apply (Rec3 _ _ _ _ (deux_Diag L_Etat C_Etat (S (S t)) (S (S (S x)))));
 elim H; clear H; unfold L_Etat, C_Etat; do 2 rewrite plus_deux;
 intros.
auto with arith.

rewrite un_pas.
generalize (H1 1 1); repeat rewrite plus_un; intros.
rewrite H2; rewrite H5; rewrite H7; auto with arith.

rewrite un_pas; rewrite H3; rewrite H4; rewrite H7; auto with arith.

clear H H0 H1 H2 H4 H5; intros H; elim H; intros.
elim H1; elim H2; clear H H0 H1 H2; intros.
generalize H2; generalize H7; clear H H0 H1 H2 H4 H5 H6 H7;
 do 2 rewrite plus_deux; intros; apply make_quatre_end; 
 auto with arith.
apply trois_quatre; auto with arith.
Qed.

End suivant_end.

End bord_gauche.


