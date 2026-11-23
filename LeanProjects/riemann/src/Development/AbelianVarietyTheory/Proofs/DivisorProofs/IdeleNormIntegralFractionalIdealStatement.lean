import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleNormIntegralFractionalIdeal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped Classical nonZeroDivisors
open GlobalTheory.Doubling (absE)
open GlobalTheory.LocIdeal (locId)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_norm_integral_fractional_ideal : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (μ : Measure (AE F E)ˣ), μ.IsHaarMeasure →
    ∀ (μi : Measure (idelesAt E (evI F))), μi.IsHaarMeasure → ∀ (s : ℕ), 2 ≤ s →
    ∀ (g : (AE F E)ˣ → ℝ), Measurable g → (∀ l, ∀ m ∈ idelesAt E (fun x : AF F => x.2), g (l * m) = g l) →
    Integrable (fun m : idelesAt E (evI F) => g m.1 * (absE F E m.1 : ℝ) ^ s) μi →
    ∀ (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 →
    Integrable (fun l : (AE F E)ˣ => g l * (if ∀ v : Pl F, compFin F E v (l : AE F E) ∈ locId v 𝔞 then (1 : ℝ) else 0) *
      (absE F E l : ℝ) ^ s) μ := by
  first | exact @GlobalTheory.TateIdelic.integrable_tate | exact GlobalTheory.TateIdelic.integrable_tate | (intros; apply GlobalTheory.TateIdelic.integrable_tate <;> assumption)
