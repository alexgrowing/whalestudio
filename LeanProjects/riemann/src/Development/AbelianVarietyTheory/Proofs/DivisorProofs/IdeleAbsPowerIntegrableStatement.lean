import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleAbsPowerIntegrable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_abs_power_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (μ : Measure (idelesAt E (evFin F v))), μ.IsHaarMeasure → ∀ C : Set (Fv F v ⊗[F] E), IsCompact C → ∀ e : ℕ, 1 ≤ e →
      IntegrableOn (fun l : idelesAt E (evFin F v) => (absE F E l.1 : ℝ) ^ e)
        {l | ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C} μ := by
  first | exact @GlobalTheory.LocTateInt.integrableOn_absE_pow | exact GlobalTheory.LocTateInt.integrableOn_absE_pow | (intros; apply GlobalTheory.LocTateInt.integrableOn_absE_pow <;> assumption)
