import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedDoubleIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_valued_double_integral : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α β : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (μa : Measure α) (μb : Measure β) [IsFiniteMeasureOnCompacts μa] [IsFiniteMeasureOnCompacts μb] [SFinite μa] [SFinite μb]
    (g : α → β → SchwartzMap V ℂ) (hg : Continuous (Function.uncurry g))
    (C : Set (α × β)) (hC : IsCompact C) (h0 : ∀ p ∉ C, g p.1 p.2 = 0)
    (S : SchwartzMap V ℂ) (hS : ∀ y, S y = ∫ a, ∫ b, g a b y ∂μb ∂μa) (l : SchwartzMap V ℂ →L[ℂ] ℂ),
    l S = ∫ a, ∫ b, l (g a b) ∂μb ∂μa := by
  first | exact @GlobalTheory.SchwInt.clm_iterated_integral | exact GlobalTheory.SchwInt.clm_iterated_integral | (intros; apply GlobalTheory.SchwInt.clm_iterated_integral <;> assumption)
