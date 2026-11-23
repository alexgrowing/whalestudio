import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentialUnipotentStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_unipotent_stabilizer : ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (Z : Matrix (Fin N) (Fin N) K) (I : Ideal (𝓞 K)), Z.det ≠ 0 → (∀ x ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → expT x ∈ stabU Z ∧ EntIn I (expT x - 1) ∧ expT x * expT (-x) = 1) ∧ ∀ x ∈ lieU Z, ∀ y ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) y → ∃ z ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) z ∧ expT x * expT y = expT z := by
  first | exact @GlobalTheory.LoopV.ExpGroup.exp_group | exact GlobalTheory.LoopV.ExpGroup.exp_group | (intros; apply GlobalTheory.LoopV.ExpGroup.exp_group <;> assumption)
