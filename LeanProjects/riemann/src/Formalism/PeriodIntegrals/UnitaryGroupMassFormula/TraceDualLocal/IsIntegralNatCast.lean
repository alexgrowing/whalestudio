import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TraceDualLocal.IsIntegralOfTmulMem

noncomputable section

namespace PI.TrDualLocW

open NumberField
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]

theorem isIntegral_natCast' (n : ℕ) : IsIntegral ℤ (n : K) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (n : ℤ))

theorem mem_S_of_pow (y : ℚ_[ℓ] ⊗[ℚ] K) (D : ℕ) (h : ∀ n : ℕ, (ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * y ^ n ∈ S K ℓ) :
    y ∈ S K ℓ := by
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have h1 : ∀ i, ‖(ℓ : ℚ_[ℓ]) ^ D * (BA K ℓ).repr y i‖ ≤ 1 := by
    intro i
    have := mem_S.1 (by simpa using h 1) i
    rwa [BA_repr_natPow_mul, PadicInt.mem_subring_iff] at this
  let wv : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℤ_[ℓ] := fun i => ⟨(ℓ : ℚ_[ℓ]) ^ D * (BA K ℓ).repr y i, h1 i⟩
  let n : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℕ := fun i => PadicInt.appr (wv i) D
  have hsp : ∀ i, ∃ e : ℤ_[ℓ], e * (ℓ : ℤ_[ℓ]) ^ D = wv i - n i :=
    fun i => Ideal.mem_span_singleton'.1 (PadicInt.appr_spec D (wv i))
  choose e he using hsp
  let u : K := ∑ i, (n i : K) * integralBasis K i
  have hu : IsIntegral ℤ u := by
    refine IsIntegral.sum _ fun i _ => ?_
    rw [integralBasis_apply]
    exact (isIntegral_natCast' _).mul (RingOfIntegers.isIntegral_coe _)
  have hℓD : (ℓ : K) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hℓ0)
  let s : K := ((ℓ : K) ^ D)⁻¹ * u
  have hsu : (ℓ : K) ^ D * s = u := mul_inv_cancel_left₀ hℓD u
  have hm : y - 1 ⊗ₜ s ∈ S K ℓ := by
    rw [mem_S]
    intro i
    rw [map_sub, Finsupp.sub_apply, BA_repr_tmul]
    have hs : (integralBasis K).repr s i = (n i : ℚ) / (ℓ : ℚ) ^ D := by
      have hs' : s = ∑ j, ((n j : ℚ) / (ℓ : ℚ) ^ D) • integralBasis K j := by
        simp only [s, u, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Rat.smul_def]
        push_cast
        ring
      rw [hs', Module.Basis.repr_sum_self]
    rw [hs]
    have h2 : ((e i * (ℓ : ℤ_[ℓ]) ^ D : ℤ_[ℓ]) : ℚ_[ℓ]) = ((wv i - n i : ℤ_[ℓ]) : ℚ_[ℓ]) := by rw [he i]
    rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_sub, PadicInt.coe_natCast, PadicInt.coe_natCast] at h2
    change _ = (ℓ : ℚ_[ℓ]) ^ D * (BA K ℓ).repr y i - _ at h2
    have hℓq : (ℓ : ℚ_[ℓ]) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hℓ0)
    have hn : (n i : ℚ_[ℓ]) = (ℓ : ℚ_[ℓ]) ^ D * (BA K ℓ).repr y i - (e i : ℚ_[ℓ]) * (ℓ : ℚ_[ℓ]) ^ D := by
      linear_combination h2
    have key : (BA K ℓ).repr y i - (((n i : ℚ) / (ℓ : ℚ) ^ D : ℚ) : ℚ_[ℓ]) = (e i : ℚ_[ℓ]) := by
      push_cast
      rw [hn]
      field_simp
      ring
    rw [key, PadicInt.mem_subring_iff]
    exact (e i).norm_le_one
  have hpow : ∀ k : ℕ, (ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * (1 ⊗ₜ s) ^ k ∈ S K ℓ := by
    intro k
    have e1 : (1 ⊗ₜ s : ℚ_[ℓ] ⊗[ℚ] K) = y + -(y - 1 ⊗ₜ s) := by ring
    rw [e1, add_pow, Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [show (ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * (y ^ j * (-(y - 1 ⊗ₜ s)) ^ (k - j) * (k.choose j : ℚ_[ℓ] ⊗[ℚ] K)) =
      ((ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * y ^ j) * ((-(y - 1 ⊗ₜ s)) ^ (k - j) * (k.choose j : ℚ_[ℓ] ⊗[ℚ] K)) by ring]
    exact Subring.mul_mem _ (h j)
      (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ hm) _) (natCast_mem _ _))
  have hint : ∀ k : ℕ, IsIntegral ℤ ((ℓ : K) ^ D * s ^ k) := by
    intro k
    apply isIntegral_of_tmul_mem (ℓ := ℓ) _ (D * k)
    · rw [show (ℓ : K) ^ (D * k) * ((ℓ : K) ^ D * s ^ k) = (ℓ : K) ^ D * ((ℓ : K) ^ D * s) ^ k by
        rw [mul_pow, pow_mul]; ring, hsu]
      exact ((isIntegral_natCast' ℓ).pow D).mul (hu.pow k)
    · have e2 : (1 ⊗ₜ ((ℓ : K) ^ D * s ^ k) : ℚ_[ℓ] ⊗[ℚ] K) = (ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * (1 ⊗ₜ s) ^ k := by
        rw [← Algebra.TensorProduct.includeRight_apply, map_mul, map_pow, map_pow, map_natCast,
          Algebra.TensorProduct.includeRight_apply]
      rw [e2]
      exact hpow k
  have hs_int : IsIntegral ℤ s := by
    refine isIntegral_of_pow_bdd s (ℓ ^ D) (pow_ne_zero _ hℓ0) fun k => ?_
    push_cast
    exact hint k
  have e3 : y = 1 ⊗ₜ s + (y - 1 ⊗ₜ s) := by ring
  rw [e3]
  exact Subring.add_mem _ (tmul_mem_S s hs_int) hm

end PI.TrDualLocW
