import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitIndicatorIntegralValue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unit_indicator_integral_value : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E)
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 → ∀ v : Pl F, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt ν w) →
    ∀ s : ℕ, 0 < s → ∀ μ : Measure (idelesAt E (evFin F v)), IsNormE E v μ →
      ∫ l : idelesAt E (evFin F v), Set.indicator {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}
          (fun l => (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ s) l ∂μ = unrFac ν 𝔞 (s : ℂ) v := by
  first | exact @GlobalTheory.UnrTate.integral_locId_eq_unrFac | exact GlobalTheory.UnrTate.integral_locId_eq_unrFac | (intros; apply GlobalTheory.UnrTate.integral_locId_eq_unrFac <;> assumption)
