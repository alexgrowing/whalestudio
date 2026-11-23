import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmEllipticCurveGaloisTorsionSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmEllipticCurve_galois_torsion_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), 0 < n → ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (ω : 𝓞 N) (C : GlobalTheory.CM.Ell H (𝓞 N) ω) (C₀ : GlobalTheory.CompRat.Curve H) (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 N) ∧ IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ ∧ ∀ a : ℤ × ℤ, ∃ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ C.P.A, y ^ n = 1 ∧ C₀.pt (GlobalTheory.CompRat.wC H a / n) ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left := by
  first | exact @GlobalTheory.TorsionModel.exists_ell_torsion_sections | exact GlobalTheory.TorsionModel.exists_ell_torsion_sections | (intros; apply GlobalTheory.TorsionModel.exists_ell_torsion_sections <;> assumption)
