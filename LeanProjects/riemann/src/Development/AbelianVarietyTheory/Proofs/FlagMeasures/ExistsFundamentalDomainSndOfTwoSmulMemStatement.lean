import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainSndOfTwoSmulMem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_snd_of_two_smul_mem' : ∀ {ι : Type} [Fintype ι] (Λ : Submodule ℤ ((ι → ℝ) × (ι → ℝ))) [DiscreteTopology Λ], Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) = ⊤ → (∀ a b, (a, b) ∈ Λ → ((0 : ι → ℝ), (2 : ℝ) • b) ∈ Λ) → ∃ D : Set (ι → ℝ), MeasurableSet D ∧ ∀ y, ∃! l, l ∈ {b : ι → ℝ | ∃ a, (a, b) ∈ Λ} ∧ y + l ∈ D := by
  first | exact @GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem | exact GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem | (intros; apply GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem <;> assumption)
