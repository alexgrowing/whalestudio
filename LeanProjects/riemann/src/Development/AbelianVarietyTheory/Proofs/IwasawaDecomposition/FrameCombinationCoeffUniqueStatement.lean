import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_combination_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (f : c.F →+* k) (x : Sp k ⟶ X) (u : Vecs Dw t k), GlobalTheory.LocM.IsFrame t f x u → (∀ cf cf' w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w → IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf' w → cf = cf') ∧ ∀ (j : Fin (letters Dw).length) (cf : Fin (Dw.mult ((letters Dw).get j).1) → k) w, (∀ m, ((letters Dw).get j).2 < m → cf m = 0) → IsCombAtG t x (u ((letters Dw).get j).1) cf w → ∃ cg : Fin (letters Dw).length → k, (∀ m, j < m → cg m = 0) ∧ cg j = cf ((letters Dw).get j).2 ∧ IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cg w := by
  first | exact @GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame | exact GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame | (intros; apply GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame <;> assumption)
