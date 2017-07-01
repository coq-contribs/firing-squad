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


Require algo.
Require Extraction.
Extract Inductive list => list [ "[]" "(::)"].
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive unit => "unit" [ "()" ].

Extract Constant autom.ref_N => "let r = ref O in ((:=) r), (fun () -> !r)".
Extract Inlined Constant autom.N => "(get_N ())".
Extraction "extracted.ml"
 autom.set_N autom.get_N algo.initial_line algo.next_line.
