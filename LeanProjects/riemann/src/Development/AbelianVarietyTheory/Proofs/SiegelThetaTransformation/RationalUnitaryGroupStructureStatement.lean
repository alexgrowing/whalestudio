import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
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
theorem _root_.GlobalTheory.T.rational_unitary_group_structure : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ e : {ga : GL (Fin T.rank) D.host.E // IsUn C.X ga} ≃ GQ T, ∀ ga, IsRatOf T ga.1 (e ga).1) ∧ (∀ (γ γ' : GA D T) ga ga', IsRatOf T ga γ → IsRatOf T ga' γ' → IsRatOf T (ga * ga') (γ * γ') ∧ IsRatOf T ga⁻¹ γ⁻¹ ∧ γ ∈ GQ T ∧ IsUn C.X ga ∧ (γ = γ' ↔ ga = ga')) ∧ (∃ e : {h : Matrix (Fin S.rank) (Fin S.rank) D.host.E // ccT h * h = 1} ≃ GQ S, ∀ h, cM (mt S (e h).1) = h.1.map (incA D)) ∧ ∀ V : HSp D, Countable (GQ V) ∧ (∀ g g' : GA D V, mt V (g * g') = mt V g * mt V g' ∧ fmt V (g * g') = fmt V g * fmt V g' ∧ fmtC V (g * g') = fmtC V g * fmtC V g' ∧ (mt V g = mt V g' → g = g')) ∧ (∀ g : GA D V, ∃ a ∈ GinfC V, ∃ f ∈ GfC V, g = a * f) ∧ (∀ a ∈ GinfC V, fmt V a = 1 ∧ fmtC V a = 1 ∧ ∀ f ∈ GfC V, a * f = f * a) ∧ ∀ (I : Ideal (𝓞 D.host.F)), I ≠ ⊥ → ∀ f ∈ GfC V, ∃ f₁ ∈ GfC V, ∃ f₂ ∈ GfC V, f = f₁ * f₂ ∧ f₁ * f₂ = f₂ * f₁ ∧ TrivAt V I f₁ ∧ TrivOff V I f₂ := by
  first | exact @GlobalTheory.Ker.Grp.rational_points_and_parts | exact GlobalTheory.Ker.Grp.rational_points_and_parts | (intros; apply GlobalTheory.Ker.Grp.rational_points_and_parts <;> assumption)
