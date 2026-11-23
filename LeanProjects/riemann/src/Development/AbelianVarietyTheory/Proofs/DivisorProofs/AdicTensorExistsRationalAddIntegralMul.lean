import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem exists_rat_sub_le (v : HeightOneSpectrum ℤ) (c d : v.adicCompletion ℚ) (hd : d ≠ 0) :
    ∃ q : ℚ, Valued.v (c - algebraMap ℚ (v.adicCompletion ℚ) q) ≤ Valued.v d := by
  have hset : {y : v.adicCompletion ℚ | Valued.v y ≤ Valued.v d} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict d} := by
    ext y; simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff]
  have hball : IsOpen {y : v.adicCompletion ℚ | Valued.v y ≤ Valued.v d} := by
    rw [hset]; exact Valued.isOpen_closedBall _ (by simpa using hd)
  have ho : IsOpen {y : v.adicCompletion ℚ | Valued.v (c - y) ≤ Valued.v d} :=
    hball.preimage (continuous_const.sub continuous_id)
  obtain ⟨q, hq⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := ℤ) (K := ℚ) v).exists_mem_open ho
    ⟨c, by simp⟩
  exact ⟨q, hq⟩

theorem exists_tmul_add_mul_isIntB : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L)
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ ⊗[ℚ] L) (D : ℤ), D ≠ 0 →
    ∃ (y : L) (ρ : v.adicCompletion ℚ ⊗[ℚ] L), IsIntB v ℓ ρ ∧
      x = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y + (D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ := by
  intro L _ _ κ ℓ v x D hD
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  have hD' : (D : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) D]
    exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hD)
  choose q hq using fun i =>
    exists_rat_sub_le v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr x i) (D : v.adicCompletion ℚ) hD'
  refine ⟨∑ i, q i • ℓ i, ∑ i, (((Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr x i -
    algebraMap ℚ (v.adicCompletion ℚ) (q i)) / D) ⊗ₜ[ℚ] ℓ i, ?_, ?_⟩
  · intro k
    rw [map_sum, Finsupp.finset_sum_apply]
    simp only [repr_tmul_apply ℓ v, ℓ.repr_self, Finsupp.single_apply, apply_ite (algebraMap ℚ (v.adicCompletion ℚ)),
      map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (D : v.adicCompletion ℚ) := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hD'
    exact (div_le_one₀ h0).2 (hq k)
  · conv_lhs => rw [eq_sum_tmul ℓ v x]
    rw [TensorProduct.tmul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcast : (D : v.adicCompletion ℚ ⊗[ℚ] L) = (D : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : L) := by
      have h := map_intCast (Algebra.TensorProduct.includeLeft : v.adicCompletion ℚ →ₐ[ℚ] v.adicCompletion ℚ ⊗[ℚ] L) D
      rw [Algebra.TensorProduct.includeLeft_apply] at h
      exact h.symm
    rw [hcast, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, Algebra.smul_def, mul_one, mul_div_cancel₀ _ hD', add_sub_cancel]

end GlobalTheory.AdicSpan
