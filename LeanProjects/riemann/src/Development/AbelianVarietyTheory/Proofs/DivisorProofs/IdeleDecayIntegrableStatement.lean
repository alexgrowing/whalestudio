import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleDecayIntegrable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_decay_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (s m : ℕ), 2 ≤ s → 0 < m →
    ∃ N : ℕ, ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure →
      Integrable (fun l => GlobalTheory.IdeleDecay.decay F E N m l * (absE F E l : ℝ) ^ s) μ := by
  first | exact @GlobalTheory.IdeleTate.integrable_decay_mul_absE | exact GlobalTheory.IdeleTate.integrable_decay_mul_absE | (intros; apply GlobalTheory.IdeleTate.integrable_decay_mul_absE <;> assumption)
