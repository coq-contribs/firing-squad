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

Require Import bib.

Section automates.

Section definitions.

Parameter N : nat.
Axiom necessaire : deux < definitions.N.

Inductive Couleur : Set :=
  | A : Couleur
  | B : Couleur
  | C : Couleur
  | L : Couleur
  | G : Couleur
  | F : Couleur.

Definition Transition_A_A (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  A
      (*B*) 
  | B => B
      (*C*) 
  | C => C
      (*L*) 
  | L => A
      (*G*) 
  | G => B
      (*F*) 
  | F => F
  end.

Definition Transition_B_A (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  F
      (*B*) 
  | B => G
      (*C*) 
  | C => C
      (*L*) 
  | L => G
      (*G*) 
  | G => C
      (*F*) 
  | F => F
  end.

Definition Transition_L_A (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  A
      (*B*) 
  | B => L
      (*C*) 
  | C => G
      (*L*) 
  | L => A
      (*G*) 
  | G => F
      (*F*) 
  | F => F
  end.

Definition Transition_A_B (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  B
      (*B*) 
  | B => B
      (*C*) 
  | C => L
      (*L*) 
  | L => G
      (*G*) 
  | G => F
      (*F*) 
  | F => F
  end.

Definition Transition_B_B (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  A
      (*B*) 
  | B => B
      (*C*) 
  | C => C
      (*L*) 
  | L => G
      (*G*) 
  | G => B
      (*F*) 
  | F => F
  end.

Definition Transition_C_B (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  A
      (*B*) 
  | B => F
      (*C*) 
  | C => F
      (*L*) 
  | L => L
      (*G*) 
  | G => L
      (*F*) 
  | F => F
  end.

Definition Transition_L_B (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  G
      (*B*) 
  | B => B
      (*C*) 
  | C => L
      (*L*) 
  | L => F
      (*G*) 
  | G => B
      (*F*) 
  | F => F
  end.

Definition Transition_G_B (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  C
      (*B*) 
  | B => F
      (*C*) 
  | C => B
      (*L*) 
  | L => C
      (*G*) 
  | G => G
      (*F*) 
  | F => F
  end.

Definition Transition_B_C (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  F
      (*B*) 
  | B => F
      (*C*) 
  | C => C
      (*L*) 
  | L => C
      (*G*) 
  | G => G
      (*F*) 
  | F => F
  end.

Definition Transition_C_C (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  A
      (*B*) 
  | B => B
      (*C*) 
  | C => C
      (*L*) 
  | L => C
      (*G*) 
  | G => B
      (*F*) 
  | F => F
  end.

Definition Transition_L_C (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  A
      (*B*) 
  | B => G
      (*C*) 
  | C => C
      (*L*) 
  | L => C
      (*G*) 
  | G => G
      (*F*) 
  | F => F
  end.

Definition Transition_A_L (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  L
      (*B*) 
  | B => L
      (*C*) 
  | C => L
      (*L*) 
  | L => G
      (*G*) 
  | G => C
      (*F*) 
  | F => F
  end.

Definition Transition_C_L (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  L
      (*B*) 
  | B => L
      (*C*) 
  | C => L
      (*L*) 
  | L => A
      (*G*) 
  | G => G
      (*F*) 
  | F => F
  end.

Definition Transition_G_L (c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  L
      (*B*) 
  | B => L
      (*C*) 
  | C => L
      (*L*) 
  | L => C
      (*G*) 
  | G => A
      (*F*) 
  | F => F
  end.


Definition Transition__G_L (c0 : Couleur) :=
  match c0 return Couleur with
  | A => 
      (*A*)  B
      (*B*) 
  | B => B
      (*C*) 
  | C => A
      (*L*) 
  | L => A
      (*G*) 
  | G => B
      (*F*) 
  | F => F
  end.


Definition Transition__G_G (c0 : Couleur) :=
  match c0 return Couleur with
  | A => 
      (*A*)  F
      (*B*) 
  | B => G
      (*C*) 
  | C => A
      (*L*) 
  | L => F
      (*G*) 
  | G => F
      (*F*) 
  | F => F
  end.

Definition Transition_A (c0 c2 : Couleur) :=
  match c0 return Couleur with
  | A => 
      (*A*)  Transition_A_A c2
      (*B*) 
  | B => Transition_B_A c2
      (*C*) 
  | C => A
      (*L*) 
  | L => Transition_L_A c2
      (*G*) 
  | G => C
      (*F*) 
  | F => F
  end.

Definition Transition_B (c0 c2 : Couleur) :=
  match c0 return Couleur with
  | A => 
      (*A*)  Transition_A_B c2
      (*B*) 
  | B => Transition_B_B c2
      (*C*) 
  | C => Transition_C_B c2
      (*L*) 
  | L => Transition_L_B c2
      (*G*) 
  | G => Transition_G_B c2
      (*F*) 
  | F => F
  end.

Definition Transition_C (c0 c2 : Couleur) :=
  match c0 return Couleur with
  | A => 
      (*A*)  B
      (*B*) 
  | B => Transition_B_C c2
      (*C*) 
  | C => Transition_C_C c2
      (*L*) 
  | L => Transition_L_C c2
      (*G*) 
  | G => B
      (*F*) 
  | F => F
  end.

Definition Transition_L (c0 c2 : Couleur) :=
  match c0 return Couleur with
  | A => 
      (*A*)  Transition_A_L c2
      (*B*) 
  | B => L
      (*C*) 
  | C => Transition_C_L c2
      (*L*) 
  | L => L
      (*G*) 
  | G => Transition_G_L c2
      (*F*) 
  | F => L
  end.

Definition Transition_G (c0 c2 : Couleur) :=
  match c2 return Couleur with
  | A => 
      (*A*)  G
      (*B*) 
  | B => G
      (*C*) 
  | C => G
      (*L*) 
  | L => Transition__G_L c0
      (*G*) 
  | G => Transition__G_G c0
      (*F*) 
  | F => G
  end.

Definition Transition (c0 c1 c2 : Couleur) :=
  match c1 return Couleur with
  | A => 
      (*A*)  Transition_A c0 c2
      (*B*) 
  | B => Transition_B c0 c2
      (*C*) 
  | C => Transition_C c0 c2
      (*L*) 
  | L => Transition_L c0 c2
      (*G*) 
  | G => Transition_G c0 c2
      (*F*) 
  | F => F
  end.

Notation Ifdec := (ifdec _ _ _) (only parsing).

Fixpoint Etat (t : nat) : nat -> Couleur :=
  fun x : nat =>
  match t return Couleur with
  | O =>
      (*O*)	
      match x return Couleur with
      | O => 
          (*O*)	 G 
          (*Sx'*)	
      | S x' =>
          ifdec _ _ _ (eq_nat_dec (S definitions.N) (S x')) G
            (ifdec _ _ _ (eq_nat_dec (S (S definitions.N)) (S x')) C L)
      end
      (*St'*)	
  | S t' =>
      match x return Couleur with
      | O => 
          (*O*)	 Transition L (Etat t' 0) (Etat t' 1)
          (*St'*)	
      | S x' => Transition (Etat t' x') (Etat t' (S x')) (Etat t' (S (S x')))
      end
  end.

End definitions.

Section cas_general.

Lemma un_pas :
 forall t x : nat,
 Etat (S t) (S x) = Transition (Etat t x) (Etat t (S x)) (Etat t (S (S x))).
intro; simpl in |- *; auto with v62.
Qed.

Lemma demi_pas :
 forall t : nat, Etat (S t) 0 = Transition L (Etat t 0) (Etat t 1).
intro; simpl in |- *; auto with v62.
Qed.

End cas_general.

Section base.

Lemma G00 : Etat 0 0 = G.
simpl in |- *; auto with v62.
Qed.

Lemma G0N : Etat 0 (S automates.N) = G.
simpl in |- *; apply Ifdec_left; auto with v62.
Qed.

Lemma C0N1 : Etat 0 (S (S automates.N)) = C.
simpl in |- *; rewrite Ifdec_right; auto with v62.
apply Ifdec_left; auto with v62.
Qed.

Lemma base_L : forall x : nat, 0 < x -> x < S automates.N -> Etat 0 x = L.
intros x Hlt; rewrite (S_pred x); auto with v62.
intros; simpl in |- *; rewrite Ifdec_right.
apply Ifdec_right.
apply sym_not_equal; apply lt_not_eq; auto with v62.

apply sym_not_equal; apply lt_not_eq; auto with v62.
Qed.

Lemma basedollar_L : forall x : nat, S (S automates.N) < x -> Etat 0 x = L.
intros; rewrite (S_pred x); auto with v62.
intros; simpl in |- *; rewrite Ifdec_right.
apply Ifdec_right.
apply lt_not_eq; auto with v62.

apply lt_not_eq; auto with v62.

apply lt_trans with (m := S automates.N); auto with v62.
Qed.

End base.

End automates.