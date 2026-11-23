import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.AdelicFactorial

theorem tendsto_factorial_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  have hle : ∀ m : ℕ, ‖(m : v.adicCompletion F)‖ ≤ 1 := fun m => by
    have := FinitePlace.norm_le_one F v (m : 𝓞 F)
    simpa using this
  set M := Ideal.absNorm v.asIdeal with hM
  have hlt : ‖(M : v.adicCompletion F)‖ < 1 := by
    have := (FinitePlace.norm_lt_one_iff_mem F v (M : 𝓞 F)).2 (Ideal.absNorm_mem _)
    simpa using this
  have hM0 : 0 < M := lt_trans one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hlt
  refine ⟨M ^ k, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (pow_pos hM0 k) hn
  rw [dist_zero_right, hc, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle c)) hk

theorem tendsto_factorial_finiteAdele (F : Type) [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => fun v : HeightOneSpectrum (𝓞 F) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    rw [tendsto_subtype_rng]
    simpa using tendsto_factorial_adicCompletion F v
  have h2 := ((RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous.tendsto _).comp h1
  exact h2

theorem exists_nat_mem_of_isOpen : ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (AF F)),
    IsOpen (U : Set (AF F)) → ∃ N : ℕ, 0 < N ∧ pairA F 0 (N : Af F) ∈ U := by
  intro F _ _ U hU
  have h : Tendsto (fun n : ℕ => pairA F 0 ((n.factorial : ℕ) : Af F)) atTop (𝓝 (0 : AF F)) :=
    (tendsto_const_nhds (x := (0 : Ainf F))).prodMk_nhds (tendsto_factorial_finiteAdele F)
  obtain ⟨n, hn⟩ := (h.eventually (hU.mem_nhds U.zero_mem)).exists
  exact ⟨n.factorial, n.factorial_pos, hn⟩

end GlobalTheory.AdelicFactorial
