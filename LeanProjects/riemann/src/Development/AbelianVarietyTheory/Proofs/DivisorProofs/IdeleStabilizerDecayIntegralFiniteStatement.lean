import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleStabilizerDecayIntegralFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_stabilizer_decay_integral_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (s : ℕ), 1 ≤ s →
    ∃ N : ℕ, ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure →
      ∫⁻ l in (GlobalTheory.IdeleTate.stab F E : Set (AE F E)ˣ),
        ENNReal.ofReal (((1 + GlobalTheory.IdeleDecay.size F E l.1) ^ N)⁻¹ * (GlobalTheory.IdeleTate.absInf F E l : ℝ) ^ s) ∂μ < ⊤ := by
  first | exact @GlobalTheory.IdeleArchBound.lintegral_stab_lt_top | exact GlobalTheory.IdeleArchBound.lintegral_stab_lt_top | (intros; apply GlobalTheory.IdeleArchBound.lintegral_stab_lt_top <;> assumption)
