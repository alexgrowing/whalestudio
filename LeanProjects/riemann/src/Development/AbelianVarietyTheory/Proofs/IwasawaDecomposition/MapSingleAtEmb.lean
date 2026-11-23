import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousChiDet
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.OneRep

noncomputable section

namespace GlobalTheory.OneRep

variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [NumberField.IsTotallyComplex E] in

theorem atEmb_zero (τ : E →+* ℂ) : atEmb τ 0 = 0 := by
  classical
  unfold atEmb; split_ifs <;> simp

omit [NumberField E] [NumberField.IsTotallyComplex E] in

theorem map_single_atEmb (τ : E →+* ℂ) (i k : Fin a) (z : ℂ) :
    (Matrix.single i k z).map (atEmb τ) = Matrix.single i k (atEmb τ z) := by
  ext p q
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [atEmb_zero]

end GlobalTheory.OneRep

end
