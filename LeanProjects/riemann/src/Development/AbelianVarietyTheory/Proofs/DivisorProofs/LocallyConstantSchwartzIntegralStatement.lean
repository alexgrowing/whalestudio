import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSchwartzIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_schwartz_integral : ∀ {P Q Y : Type} [TopologicalSpace P] [CompactSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
    [TopologicalSpace Q] [T2Space Q] [MeasurableSpace Q] [OpensMeasurableSpace Q] [TopologicalSpace Y]
    (μP : Measure P) [IsFiniteMeasure μP] (μQ : Measure Q) [IsFiniteMeasureOnCompacts μQ] (f : P → Q → Y → ℂ)
    (g : Q → ℂ) (C : Set Q), IsCompact C → IsLocallyConstant (Function.uncurry f) → (∀ p q, f p q ∈ SB Y) →
    (∀ p q, q ∉ C → f p q = 0) → Continuous g → ∀ L : (Y → ℂ) → ℂ,
    (∀ a ∈ SB Y, ∀ a' ∈ SB Y, L (a + a') = L a + L a') → (∀ (c : ℂ), ∀ a ∈ SB Y, L (c • a) = c * L a) →
    (fun y => ∫ p, ∫ q, f p q y * g q ∂μQ ∂μP) ∈ SB Y ∧
      L (fun y => ∫ p, ∫ q, f p q y * g q ∂μQ ∂μP) = ∫ p, ∫ q, L (f p q) * g q ∂μQ ∂μP := by
  first | exact @GlobalTheory.ConeBump.integ_mem_SB_and_map | exact GlobalTheory.ConeBump.integ_mem_SB_and_map | (intros; apply GlobalTheory.ConeBump.integ_mem_SB_and_map <;> assumption)
