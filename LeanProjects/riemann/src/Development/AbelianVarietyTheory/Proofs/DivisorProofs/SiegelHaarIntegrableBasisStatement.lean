import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelHaarIntegrableBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_haar_integrable_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (f : (Fin n → AE F E) → ℂ) (μ : @Measure (Fin n → AE F E) (borel _)), GlobalTheory.SiegelAvg.IsHaarB μ →
    (∀ ν : @Measure (Fin n × Fin (Module.finrank F E) → AF F) (borel _), GlobalTheory.SiegelAvg.IsHaarB ν →
      (letI : MeasurableSpace (Fin n × Fin (Module.finrank F E) → AF F) := borel _; Integrable (fun t => f (GlobalTheory.SiegelConv.basisMap F E n t)) ν)) →
    (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable f μ) := by
  first | exact @GlobalTheory.SiegelConv.integrable_basisMap_main | exact GlobalTheory.SiegelConv.integrable_basisMap_main | (intros; apply GlobalTheory.SiegelConv.integrable_basisMap_main <;> assumption)
