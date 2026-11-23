import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralIdeleMajorantFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_idele_majorant_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (μ : Measure (AE F E)ˣ), μ.IsHaarMeasure →
    ∀ s : ℝ, 1 < s → ∀ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U → ∃ N : ℕ,
      ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) ∂μ < ⊤ := by
  first | exact @GlobalTheory.TateConv.majorant_inv_lintegral_lt_top | exact GlobalTheory.TateConv.majorant_inv_lintegral_lt_top | (intros; apply GlobalTheory.TateConv.majorant_inv_lintegral_lt_top <;> assumption)
