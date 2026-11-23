import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaInnerProductEqRealTorusMean
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaInnerProduct_eq_realTorusMean : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f', C.IsTh f → C.IsTh f' → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → (∃ Fd : Set (WR C.X S.rank), IsAddFundamentalDomain (latR C.X S.rank N) Fd volume) ∧ ∀ Fd : Set (WR C.X S.rank), IsAddFundamentalDomain (latR C.X S.rank N) Fd volume → ∀ F : WR C.X S.rank → ℂ, (∀ w, IsRealPt w → f w * conj (f' w) = F (C.realPt w)) → ipO μ 𝓕 f f' = ((volume Fd).toReal : ℂ)⁻¹ * ∫ v in Fd, F v := by
  first | exact @GlobalTheory.Ker.TorusMean.ipO_eq_mean | exact GlobalTheory.Ker.TorusMean.ipO_eq_mean | (intros; apply GlobalTheory.Ker.TorusMean.ipO_eq_mean <;> assumption)
