import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaInnerEqConstMulTestInner
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
theorem _root_.GlobalTheory.T.exists_vacua_inner_eq_const_mul_testInner : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ φ' : TF S.rank C.g, SW.IsSB φ → SW.IsSB φ' → ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ') = a * ip φ φ' := by
  first | exact @GlobalTheory.KerVacIp.ip_vacua | exact GlobalTheory.KerVacIp.ip_vacua | (intros; apply GlobalTheory.KerVacIp.ip_vacua <;> assumption)
