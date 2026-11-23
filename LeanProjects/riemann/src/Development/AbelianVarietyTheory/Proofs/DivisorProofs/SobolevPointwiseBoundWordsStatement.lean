import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevPointwiseBoundWords
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
theorem _root_.GlobalTheory.T.sobolev_pointwise_bound_words : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (D : ℕ) (C : ℝ), (∀ l ∈ L, l.length ≤ D ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ Φ ∈ schA F κ, ∀ x : κ → AF F, ‖Φ x‖ₑ ^ 2 ≤ ENNReal.ofReal C * ∑ l ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l Φ (x + GlobalTheory.SobClass.archInc F y)‖ₑ ^ 2 := by
  first | exact @GlobalTheory.SliceSob.slice_sobolev | exact GlobalTheory.SliceSob.slice_sobolev | (intros; apply GlobalTheory.SliceSob.slice_sobolev <;> assumption)
