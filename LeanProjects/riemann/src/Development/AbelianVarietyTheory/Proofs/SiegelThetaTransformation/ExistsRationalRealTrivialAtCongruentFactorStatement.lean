import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalRealTrivialAtCongruentFactor
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
theorem _root_.GlobalTheory.T.exists_rational_real_trivialAt_congruent_factor : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (I : Ideal (𝓞 D.host.F)) (M : ℕ), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) → I ≠ ⊥ → 0 < M → ∀ g : GA D V, ∃ γ ∈ GQ V, ∃ a ∈ GinfC V, ∃ g' ∈ GfC V, ∃ k ∈ GfC V, g = γ * a * g' * k ∧ TrivAt V I g' ∧ TrivOff V I k ∧ CongK V L M k ∧ ∀ J : Ideal (𝓞 D.host.E), (M : 𝓞 D.host.E) ∈ J → ∀ u ∈ hatV L, fmt V k *ᵥ u - u ∈ hatV (J • L) := by
  first | exact @GlobalTheory.Ker.CutAt.exists_rat_real_trivAt_cong | exact GlobalTheory.Ker.CutAt.exists_rat_real_trivAt_cong | (intros; apply GlobalTheory.Ker.CutAt.exists_rat_real_trivAt_cong <;> assumption)
