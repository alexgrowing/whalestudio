import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_ideles_power_decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (μ : Measure (idelesAt E (evI F))), μ.IsHaarMeasure → ∀ z : ℕ, 1 ≤ z →
    ∃ N : ℕ, Integrable (fun l : idelesAt E (evI F) => (GlobalTheory.Doubling.absE F E l.1 : ℝ) ^ z / (1 + ∑ w, ‖piInf (B.emb w) (l.1 : AE F E)‖) ^ N) μ := by
  first | exact @GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div | exact GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div | (intros; apply GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div <;> assumption)
