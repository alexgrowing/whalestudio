import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_qkPoints_complex_degeneration : Known → ∀ (K : Type) [Field K] [NumberField K] (σ₁ : K →+* ℂ) (D₁ : Out.DegPre K) (DC : Out.DegPre ℂ) (p : Out.IsPullDeg σ₁ D₁ DC) (n N : ℕ), 0 < n → 0 < N → DC.TauBimult → (∀ y, DC.c y ^ n = 1) → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (i : K →+* K₂) (σ₂ : K₂ →+* ℂ) (D₂ : Out.DegPre K₂) (q : Out.IsPullDeg i D₁ D₂) (p₂ : Out.IsPullDeg σ₂ D₂ DC), σ₂.comp i = σ₁ ∧ prj p₂ ≫ prj q = prj p ∧ ∀ k : ℕ, k ∣ N → ∀ x : Out.QkPt DC (FractionRing ℂ) k, ∃ x₂, GlobalTheory.ArcPull.IsPullQk p₂ x₂ x := by
  first | exact @GlobalTheory.QkNumberField.exists_numberField_qk | exact GlobalTheory.QkNumberField.exists_numberField_qk | (intros; apply GlobalTheory.QkNumberField.exists_numberField_qk <;> assumption)
