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


Require Export bib.
Require Export autom.
Require Export final.
Require Export List.
Require Export Arith.

(* An efficient way to compute [Etat n p] by a single list *)
(* Addition to FIRING_SQUAD by P. Letouzey, nov 2001 *)

Fixpoint next_line_accum (a : Couleur) (l : list Couleur) {struct l} :
 list Couleur :=
  match l with
  | nil => nil
  | a' :: l' =>
      match l' with
      | nil => Transition a a' G :: nil
      | a'' :: l'' => Transition a a' a'' :: next_line_accum a' l'
      end
  end. 

Definition next_line := next_line_accum L.

Fixpoint constant (c : Couleur) (n : nat) {struct n} : 
 list Couleur := match n with
                 | O => nil
                 | S n => c :: constant c n
                 end.

(* Don't remove the dummy argument. It is used to protect from evaluation after 
   extraction. *)

Definition initial_line (_ : nat) := G :: constant L autom.N.

Fixpoint nth_line (n : nat) : list Couleur :=
  match n with
  | O => initial_line 0
  | S n => next_line (nth_line n)
  end. 

Section NTH.

Variable dft : Couleur.

Lemma constant_correct :
 forall (c : Couleur) (n p : nat), p < n -> nth p (constant c n) dft = c. 
induction n; simpl; auto.
intros; inversion H.
intro p; case p; clear p; simpl; auto.
intro p; intros; apply IHn; auto with arith.
Qed.

Lemma initial_line_O : nth 0 (initial_line 0) dft = G.
simpl; auto.
Qed.

Lemma initial_line_S :
 forall p : nat, 0 < p -> p <= autom.N -> nth p (initial_line 0) dft = L.
intro p; case p.
intro H; inversion H.
simpl; intros; apply constant_correct; auto with arith.
Qed.

Lemma nth_next_line_accum_O :
 forall (c : Couleur) (l : list Couleur),
 1 < length l ->
 nth 0 (next_line_accum c l) dft = Transition c (nth 0 l dft) (nth 1 l dft). 
intros c l; case l.
simpl; intro H; inversion H.
simpl; intros a' l'; case l'.
simpl; intro H; absurd (1 < 1); auto with arith.
simpl; auto.
Qed.

Lemma nth_next_line_accum_fin :
 forall (l : list Couleur) (c : Couleur) (p : nat),
 S (S p) = length l ->
 nth (S p) (next_line_accum c l) dft =
 Transition (nth p l dft) (nth (S p) l dft) G.
simple induction l.
simpl; intros c p H; inversion H.
clear l; intros c l.
case l.
intros; inversion H0.
intros a' l'; case l'.
intros.
inversion H0; auto.
intros.
simpl in H0; inversion H0.
simpl.
simpl in H.
rewrite (H dft (length l0)); auto.
Qed.

Lemma nth_next_line_accum_milieu :
 forall (l : list Couleur) (c : Couleur) (p : nat),
 S (S p) < length l ->
 nth (S p) (next_line_accum c l) dft =
 Transition (nth p l dft) (nth (S p) l dft) (nth (S (S p)) l dft).
simple induction l.
simpl; intros c p H; inversion H.
clear l; intros c l.
case l.
intros; simpl in H0; absurd (S (S p) <= 1); auto with arith.
intros a' l'; case l'.
intros.
simpl in H0; inversion H0; absurd (S (S (S p)) <= 1); auto with arith.
simpl; intros.
generalize H0.
case p; auto.
intros.
rewrite (H dft n); auto with arith.
Qed.

Lemma length_constant :
 forall (p : nat) (c : Couleur), length (constant c p) = p. 
induction p; simpl; auto.
Qed.

Lemma length_initial_line : length (initial_line 0) = S autom.N.
simpl.
rewrite length_constant; auto.
Qed.

Lemma length_next_line :
 forall l : list Couleur, length (next_line l) = length l.
simple induction l; unfold next_line; simpl; auto.
intros a' l'; case l'; simpl; auto.
intros a'' l''; case l''; simpl; auto.
Qed.

Lemma length_nth_line : forall n : nat, length (nth_line n) = S autom.N.
induction n.
apply length_initial_line; auto.
simpl.
rewrite length_next_line; auto.
Qed.

Theorem nth_nth_line_is_etat :
 forall n p : nat,
 n <= double autom.N -> p <= autom.N -> nth p (nth_line n) dft = Etat n p.
induction n.
intro p; case p.
simpl; auto.
clear p; intros p H Hp.
rewrite base_L; auto with arith.
apply initial_line_S; auto with arith.
simpl.
intro p; case p; clear p; unfold next_line; intros.
rewrite nth_next_line_accum_O.
rewrite (IHn 0); auto with arith.
rewrite (IHn 1); auto with arith.
apply le_lt_trans with 2; auto; exact necessaire.
rewrite length_nth_line; simpl.
apply lt_n_S.
apply le_lt_trans with 2; auto; exact necessaire.
inversion H0.
rewrite nth_next_line_accum_fin. 
rewrite (IHn n0); auto with arith.
rewrite (IHn (S n0)); auto with arith.
rewrite H2.
elim vert_droite.
unfold basic.G_Etat.
intro.
generalize H; case n; intros.
rewrite G0N; auto.
rewrite <- (H1 n1); auto with arith.
apply le_S_n.
rewrite <- S_pred; auto with arith.
unfold double; apply lt_le_trans with autom.N; auto with arith.
apply lt_trans with 2; auto; exact necessaire.
rewrite length_nth_line; simpl; auto.
rewrite nth_next_line_accum_milieu. 
rewrite (IHn n0); auto with arith.
rewrite (IHn (S n0)); auto with arith.
rewrite (IHn (S (S n0))); auto with arith.
rewrite <- H1; auto with arith.
rewrite length_nth_line; simpl; auto.
rewrite <- H1; auto with arith.
Qed.

End NTH.

Lemma is_constant :
 forall (dft c : Couleur) (l : list Couleur),
 (forall p : nat, p < length l -> nth p l dft = c) ->
 l = constant c (length l).
induction l; simpl; auto.
intros.
rewrite (H 0); auto with arith.
apply (f_equal2 (A1:=Couleur) (A2:=list Couleur)); auto.
apply IHl.
intros; rewrite <- (H (S p)); auto with arith.
Qed.

Theorem nth_line_2N_is_fire :
 nth_line (double autom.N) = constant F (S autom.N).
cut (length (nth_line (double autom.N)) = S autom.N);
 [ intro Eq | apply length_nth_line; auto ].
rewrite <- Eq.
apply (is_constant L).
rewrite Eq.
intros; rewrite nth_nth_line_is_etat; auto with arith.
elim firing_squad; unfold basic.G_Etat, basic.F_Etat.
intros.
rewrite <- (H0 p); simpl; auto with arith.
Qed.
