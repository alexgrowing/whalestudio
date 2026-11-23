import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldGeneratedSpec
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_field_generated_spec : ∀ {A : Type} [CommRing A] (x : Sp A), ∃ φ : A →+* (Sp A).residueField x,
    spMap φ = (Sp A).fromSpecResidueField x ∧ Subfield.closure (Set.range φ) = ⊤ := by
  first | exact @GlobalTheory.residueField_spMap | exact GlobalTheory.residueField_spMap | (intros; apply GlobalTheory.residueField_spMap <;> assumption)
