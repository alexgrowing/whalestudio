import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousKernelIntegralProd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_kernel_integral_prod : ∀ {α β : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (μa : Measure α) (μb : Measure β) [IsFiniteMeasureOnCompacts μa] [IsFiniteMeasureOnCompacts μb]
    [μa.IsOpenPosMeasure] [μb.IsOpenPosMeasure] [SFinite μa] [SFinite μb]
    (F : α → β → ℂ) (hF : Continuous (Function.uncurry F)) (C : Set (α × β)) (hC : IsCompact C)
    (h0 : ∀ p ∉ C, F p.1 p.2 = 0) (c : ℂ) (hpos : ∀ a b, 0 ≤ (starRingEnd ℂ c * F a b).re) (a₀ : α) (b₀ : β)
    (h₀ : 0 < (starRingEnd ℂ c * F a₀ b₀).re),
    ∫ a, ∫ b, F a b ∂μb ∂μa ≠ 0 := by
  first | exact @GlobalTheory.bump_iterated_integral_ne_zero | exact GlobalTheory.bump_iterated_integral_ne_zero | (intros; apply GlobalTheory.bump_iterated_integral_ne_zero <;> assumption)
