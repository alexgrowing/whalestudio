import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroDualThetaLiftRelevant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_dual_theta_lift_relevant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')), IsTriple B G X om om' →
    IsTriple B (reG G V V' W) X om om' → G.q = 0 → (∃ Φ' ∈ PolData B (reG G V V' W).M', (reG G V V' W).M'.I om' Φ' ≠ 0) →
    ∃ Φ' ∈ PolData B G.M', G.M'.I om' Φ' ≠ 0 := by
  first | exact @GlobalTheory.ThKAnisoSmallReG.nonZero_reG | exact GlobalTheory.ThKAnisoSmallReG.nonZero_reG | (intros; apply GlobalTheory.ThKAnisoSmallReG.nonZero_reG <;> assumption)
