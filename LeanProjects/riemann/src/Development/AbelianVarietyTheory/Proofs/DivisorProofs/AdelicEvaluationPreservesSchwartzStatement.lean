import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicEvaluationPreservesSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_evaluation_preserves_schwartz : ∀ (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2), ∀ Φ ∈ schA F (Fin n × Fin d),
    evA F hd Φ ∈ schA F (Fin n × Fin d₁) := by
  first | exact @GlobalTheory.ThK.PlaneEv.SchMap.evA_mem_schA | exact GlobalTheory.ThK.PlaneEv.SchMap.evA_mem_schA | (intros; apply GlobalTheory.ThK.PlaneEv.SchMap.evA_mem_schA <;> assumption)
