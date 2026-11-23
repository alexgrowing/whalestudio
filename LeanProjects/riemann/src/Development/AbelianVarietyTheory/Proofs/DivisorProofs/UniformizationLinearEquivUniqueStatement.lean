import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationLinearEquivUnique
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_linear_equiv_unique : ∀ (R : Type) [CommRing R] (f : R →+* ℂ) (P₀ : Out.PolAV (Sp R)) (Q Q' : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ P₀.A.left) (ψ' : Q'.A.left ⟶ P₀.A.left) (g : ℕ) (u : HolUnif Q.A Q.L g) (u' : HolUnif Q'.A Q'.L g) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), Q.g = g → Q'.g = g → GlobalTheory.IsPolFibre f P₀ Q ψ → GlobalTheory.IsPolFibre f P₀ Q' ψ' → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∃ F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ) ∧ ∀ z w, hermForm Hm' (F z) (F w) = hermForm Hm z w := by
  first | exact @GlobalTheory.UnifTransfer.exists_linearEquiv_of_isPolFibre | exact GlobalTheory.UnifTransfer.exists_linearEquiv_of_isPolFibre | (intros; apply GlobalTheory.UnifTransfer.exists_linearEquiv_of_isPolFibre <;> assumption)
