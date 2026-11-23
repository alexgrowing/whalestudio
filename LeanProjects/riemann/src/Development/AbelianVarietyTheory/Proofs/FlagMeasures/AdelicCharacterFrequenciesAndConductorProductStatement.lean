import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_character_frequencies_and_conductor_product : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ ψ : AddChar (AF I.F) ℂ, IsCharAF I.F ψ → ∃ (lamv : InfinitePlace I.F → ℝ) (m : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) → ℤ), (∀ v, lamv v ≠ 0) ∧ (∀ x, psiInf I.F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) ∧ (Function.support m).Finite ∧ (∀ u (t : Fv I.F u), (∀ s ∈ u.adicCompletionIntegers I.F, psiV I.F ψ u (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp (m u)) ∧ ∏ᶠ u, (Ideal.absNorm u.asIdeal : ℝ) ^ m u = |(discr I.F : ℝ)| * ∏ v, |lamv v| := by
  first | exact @GlobalTheory.AdeleCharConductor.real_part_and_conductors | exact GlobalTheory.AdeleCharConductor.real_part_and_conductors | (intros; apply GlobalTheory.AdeleCharConductor.real_part_and_conductors <;> assumption)
