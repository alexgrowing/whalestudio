import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddNormPowLeSumLinearFormPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_norm_pow_le_sum_linearForm_pow : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ), ∃ (K : ℕ) (l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (C : ℝ), (∀ j, ‖l j‖ ≤ 1) ∧ ∀ y, (1 + ‖y‖) ^ N ≤ C * (1 + ∑ j, |l j y| ^ N) := by
  first | exact @GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow | exact GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow | (intros; apply GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow <;> assumption)
