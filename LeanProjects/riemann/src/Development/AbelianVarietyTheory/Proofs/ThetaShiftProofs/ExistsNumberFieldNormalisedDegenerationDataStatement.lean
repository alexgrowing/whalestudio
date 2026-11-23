import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldNormalisedDegenerationData
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_normalised_degenerationData : Known → ∀ (K : Type) [Field K] [NumberField K] (σ₁ : K →+* ℂ) (P : Out.PolAV (Sp K)) (DC : Out.DegPre ℂ) (φ : DC.P.A.left ⟶ P.A.left) (n : ℕ), 0 < n → IsPolFibre σ₁ P DC.P φ → DC.PsiEven → DC.TauBimult → TauCan DC n → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (i : K →+* K₂) (σ₂ : K₂ →+* ℂ) (D₂ : Out.DegPre K₂) (p : Out.IsPullDeg σ₂ D₂ DC) (ψ : D₂.P.A.left ⟶ P.A.left), σ₂.comp i = σ₁ ∧ IsPolFibre i P D₂.P ψ ∧ prj p ≫ ψ = φ := by
  first | exact @GlobalTheory.NormDescent.exists_numberField_pre | exact GlobalTheory.NormDescent.exists_numberField_pre | (intros; apply GlobalTheory.NormDescent.exists_numberField_pre <;> assumption)
