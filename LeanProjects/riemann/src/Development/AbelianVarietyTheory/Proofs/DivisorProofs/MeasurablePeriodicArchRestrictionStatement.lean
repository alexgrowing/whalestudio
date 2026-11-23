import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurablePeriodicArchRestriction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSlice
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_periodic_arch_restriction : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (a : ℕ) (C : ℝ), ∀ m : ℕ, 1 ≤ m → ∀ f : (κ → AF F) → ENNReal, (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → f (x + (m : AF F) • a') = f x) → ∀ x : κ → AF F, Measurable (fun y : κ → mixedEmbedding.mixedSpace F => f (x + GlobalTheory.SobClass.archInc F y)) → ∫⁻ y : κ → mixedEmbedding.mixedSpace F, f (x + GlobalTheory.SobClass.archInc F y) ≤ ENNReal.ofReal (C * (m : ℝ) ^ a) * ∫⁻ z, f z ∂μ := by
  first | exact @GlobalTheory.SobClass.ClassMeas.class_meas | exact GlobalTheory.SobClass.ClassMeas.class_meas | (intros; apply GlobalTheory.SobClass.ClassMeas.class_meas <;> assumption)
