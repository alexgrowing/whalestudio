import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_power_norm_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (μ : Measure (idelesAt E (evFin F v))), IsNormE E v μ → ∀ (C : Set (Fv F v ⊗[F] E)), IsCompact C → ∀ z : ℕ, 1 ≤ z →
      Integrable (fun l : idelesAt E (evFin F v) =>
        C.indicator (fun _ => ((GlobalTheory.Doubling.absE F E l.1 : ℝ)) ^ z) (compFin F E v l.1)) μ := by
  first | exact @GlobalTheory.LocTateInt.integrable_indicator_absE_pow | exact GlobalTheory.LocTateInt.integrable_indicator_absE_pow | (intros; apply GlobalTheory.LocTateInt.integrable_indicator_absE_pow <;> assumption)
