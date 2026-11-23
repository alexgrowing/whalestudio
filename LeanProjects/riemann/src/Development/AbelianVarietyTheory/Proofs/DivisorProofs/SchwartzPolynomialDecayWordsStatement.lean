import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPolynomialDecayWords
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
theorem _root_.GlobalTheory.T.schwartz_polynomial_decay_words : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ N : ℕ, ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (K : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F), ‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N ≤ K * ∑ l ∈ L, ‖wordH ψ l Φ z‖ := by
  first | exact @GlobalTheory.SobClass.Weight.weight_le_words | exact GlobalTheory.SobClass.Weight.weight_le_words | (intros; apply GlobalTheory.SobClass.Weight.weight_le_words <;> assumption)
