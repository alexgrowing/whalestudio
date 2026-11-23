import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
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
theorem _root_.GlobalTheory.T.thetaFunction_fundamentalDomain_innerProduct_basic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f, C.IsTh f → (∃ b : ℝ, ∀ w, ‖f w‖ ≤ b) ∧ (ipO μ 𝓕 f f = 0 → f = 0) ∧ ipO μ 𝓕 f f = nrm2 μ 𝓕 f ∧ ∀ f', C.IsTh f' → IntegrableOn (fun w => f w * conj (f' w)) 𝓕 μ ∧ ipO μ 𝓕 f' f = conj (ipO μ 𝓕 f f') ∧ (∀ a : ℂ, ipO μ 𝓕 (a • f) f' = a * ipO μ 𝓕 f f') ∧ (∀ f'', C.IsTh f'' → ipO μ 𝓕 (f + f') f'' = ipO μ 𝓕 f f'' + ipO μ 𝓕 f' f'') ∧ (∀ w, ipO μ 𝓕 (C.rho w f) (C.rho w f') = ipO μ 𝓕 f f') ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ p, ipO μ 𝓕 (om p f) (om p f') = ipO μ 𝓕 f f' := by
  first | exact @GlobalTheory.Ker.ScalarProduct.ip_basic | exact GlobalTheory.Ker.ScalarProduct.ip_basic | (intros; apply GlobalTheory.Ker.ScalarProduct.ip_basic <;> assumption)
