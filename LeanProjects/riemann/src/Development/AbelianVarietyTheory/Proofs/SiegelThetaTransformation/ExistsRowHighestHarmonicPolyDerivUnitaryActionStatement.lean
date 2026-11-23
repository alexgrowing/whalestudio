import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowHighest_harmonic_polyDeriv_unitaryAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ P ∈ Harm.rowHighest ℂ k k', ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ F : (Fin n → Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv P (letterDir X hr idx) (fun z => F (hAct X idx h z)) 0 = I2.polyDeriv P' (letterDir X hr idx) F 0 := by
  first | exact @GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct | exact GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct | (intros; apply GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct <;> assumption)
