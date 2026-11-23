import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTameCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_tame_character : GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → labAt hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u := by
  first | exact @GlobalTheory.TameCharLabel.label_reduction | exact GlobalTheory.TameCharLabel.label_reduction | (intros; apply GlobalTheory.TameCharLabel.label_reduction <;> assumption)
