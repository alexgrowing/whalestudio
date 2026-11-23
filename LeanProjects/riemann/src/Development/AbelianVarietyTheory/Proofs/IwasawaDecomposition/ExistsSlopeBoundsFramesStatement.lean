import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSlopeBoundsFrames
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_slope_bounds_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {l : Level H} (c : Coeff l) {X : Scheme.{0}} (t : SAB H X) (p : ℕ), p.Prime → ∃ m : ℕ, ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (f : c.F →+* C) (x : Sp C ⟶ X) (u : Vecs Dw t C), GlobalTheory.LocM.IsFrame t f x u → ∀ (j : Fin (letters Dw).length), ∃ a : ℝ, 1 ≤ a ∧ a ≤ (p : ℝ) ^ m ∧ ∀ r ∈ Guard.grSet t x (latDR t x) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) j, a * r ∈ Guard.grSet t x (latDR t x) (u ((letters Dw).get j).1) ((letters Dw).get j).2 := by
  first | exact @GlobalTheory.ShFam.Pad.LieScale.scale | exact GlobalTheory.ShFam.Pad.LieScale.scale | (intros; apply GlobalTheory.ShFam.Pad.LieScale.scale <;> assumption)
