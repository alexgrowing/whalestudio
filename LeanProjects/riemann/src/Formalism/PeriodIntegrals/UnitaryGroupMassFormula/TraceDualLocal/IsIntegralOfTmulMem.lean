import Mathlib

noncomputable section

namespace PI.TrDualLocW

open NumberField
open scoped TensorProduct

variable (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]

def BA : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) :=
  Algebra.TensorProduct.basis ℚ_[ℓ] (integralBasis K)

variable {K ℓ}

theorem BA_apply (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) : BA K ℓ i = 1 ⊗ₜ integralBasis K i :=
  Algebra.TensorProduct.basis_apply _ i

theorem BA_repr_tmul (x : K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (BA K ℓ).repr (1 ⊗ₜ x) i = (((integralBasis K).repr x i : ℚ) : ℚ_[ℓ]) := by
  simp [BA, Finsupp.mapRange_apply]

theorem coord_int (x : K) (hx : IsIntegral ℤ x) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ∃ z : ℤ, (integralBasis K).repr x i = z := by
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = x := ⟨⟨x, (mem_integralClosure_iff ℤ K).2 hx⟩, rfl⟩
  rw [integralBasis_repr_apply]
  exact ⟨_, rfl⟩

theorem BA_repr_natPow_mul (D : ℕ) (x : ℚ_[ℓ] ⊗[ℚ] K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (BA K ℓ).repr ((ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * x) i = (ℓ : ℚ_[ℓ]) ^ D * (BA K ℓ).repr x i := by
  rw [show ((ℓ : ℚ_[ℓ] ⊗[ℚ] K)) ^ D * x = ((ℓ : ℚ_[ℓ]) ^ D) • x by
    rw [Algebra.smul_def, map_pow, map_natCast]]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

variable (K ℓ)

def S : Subring (ℚ_[ℓ] ⊗[ℚ] K) where
  carrier := {x | ∀ i, (BA K ℓ).repr x i ∈ PadicInt.subring ℓ}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro a b ha hb i
    rw [map_add, Finsupp.add_apply]
    exact add_mem (ha i) (hb i)
  neg_mem' := by
    intro a ha i
    rw [map_neg, Finsupp.neg_apply]
    exact neg_mem (ha i)
  one_mem' := by
    intro i
    rw [Algebra.TensorProduct.one_def, BA_repr_tmul]
    obtain ⟨z, hz⟩ := coord_int (1 : K) isIntegral_one i
    rw [hz, Rat.cast_intCast]
    exact intCast_mem _ z
  mul_mem' := by
    intro a b ha hb i
    have e : a * b = ∑ j, ∑ k, ((BA K ℓ).repr a j * (BA K ℓ).repr b k) • (BA K ℓ j * BA K ℓ k) := by
      conv_lhs => rw [← (BA K ℓ).sum_repr a, ← (BA K ℓ).sum_repr b]
      rw [Finset.sum_mul_sum]
      simp only [smul_mul_smul_comm]
    rw [e]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    refine Subring.sum_mem _ fun j _ => Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (Subring.mul_mem _ (ha j) (hb k)) ?_
    rw [BA_apply, BA_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, BA_repr_tmul]
    have hi : IsIntegral ℤ (integralBasis K j * integralBasis K k) := by
      rw [integralBasis_apply, integralBasis_apply]
      exact (RingOfIntegers.isIntegral_coe _).mul (RingOfIntegers.isIntegral_coe _)
    obtain ⟨z, hz⟩ := coord_int _ hi i
    rw [hz, Rat.cast_intCast]
    exact intCast_mem _ z

variable {K ℓ}

theorem mem_S {x : ℚ_[ℓ] ⊗[ℚ] K} : x ∈ S K ℓ ↔ ∀ i, (BA K ℓ).repr x i ∈ PadicInt.subring ℓ := Iff.rfl

theorem tmul_mem_S (x : K) (hx : IsIntegral ℤ x) : (1 ⊗ₜ x : ℚ_[ℓ] ⊗[ℚ] K) ∈ S K ℓ := by
  rw [mem_S]
  intro i
  rw [BA_repr_tmul]
  obtain ⟨z, hz⟩ := coord_int x hx i
  rw [hz, Rat.cast_intCast]
  exact intCast_mem _ z

theorem isIntegral_of_pow_bdd (s : K) (d : ℕ) (hd : d ≠ 0) (h : ∀ n : ℕ, IsIntegral ℤ ((d : K) * s ^ n)) :
    IsIntegral ℤ s := by
  let T : Submodule ℤ K :=
    (Submodule.span ℤ (Set.range (integralBasis K))).map (LinearMap.mulLeft ℤ ((d : K)⁻¹))
  have hT : T.FG := (Submodule.fg_span (Set.finite_range _)).map _
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ {s}) ≤ T := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, Submonoid.mem_closure_singleton] at hx
    obtain ⟨n, rfl⟩ := hx
    refine ⟨(d : K) * s ^ n, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_span_integralBasis]
      exact ⟨⟨_, (mem_integralClosure_iff ℤ K).2 (h n)⟩, rfl⟩
    · show (d : K)⁻¹ * ((d : K) * s ^ n) = s ^ n
      rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hd)]
  exact IsIntegral.of_mem_of_fg _ (hT.of_le hle) s (Algebra.self_mem_adjoin_singleton ℤ s)

theorem isIntegral_of_tmul_mem (X : K) (E : ℕ) (hX : IsIntegral ℤ ((ℓ : K) ^ E * X))
    (hS : (1 ⊗ₜ X : ℚ_[ℓ] ⊗[ℚ] K) ∈ S K ℓ) : IsIntegral ℤ X := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have hw : ∀ i, ∃ w : ℤ, (integralBasis K).repr X i = w := by
    intro i
    obtain ⟨z, hz⟩ := coord_int _ hX i
    have hz' : (integralBasis K).repr ((ℓ : K) ^ E * X) i = (ℓ : ℚ) ^ E * (integralBasis K).repr X i := by
      rw [show ((ℓ : K)) ^ E * X = ((ℓ : ℚ) ^ E) • X by
        rw [Algebra.smul_def, map_pow, map_natCast]]
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hn : ‖(((integralBasis K).repr X i : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
      have := mem_S.1 hS i
      rwa [BA_repr_tmul, PadicInt.mem_subring_iff] at this
    have hdiv : ((ℓ : ℤ) ^ E : ℤ) ∣ z := by
      rw [← Padic.norm_int_le_pow_iff_dvd]
      have hq : ((z : ℚ_[ℓ])) = (ℓ : ℚ_[ℓ]) ^ E * (((integralBasis K).repr X i : ℚ) : ℚ_[ℓ]) := by
        have h2 : ((z : ℚ) : ℚ_[ℓ]) = (((ℓ : ℚ) ^ E * (integralBasis K).repr X i : ℚ) : ℚ_[ℓ]) := by
          rw [← hz', hz]
        push_cast at h2
        exact h2
      rw [hq, norm_mul, Padic.norm_p_pow]
      calc (ℓ : ℝ) ^ (-(E : ℤ)) * ‖(((integralBasis K).repr X i : ℚ) : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(E : ℤ)) * 1 :=
            mul_le_mul_of_nonneg_left hn (by positivity)
        _ = _ := mul_one _
    obtain ⟨w, hw⟩ := hdiv
    refine ⟨w, ?_⟩
    have h1 : (ℓ : ℚ) ^ E * (integralBasis K).repr X i = (ℓ : ℚ) ^ E * w := by
      rw [← hz', hz, hw]
      push_cast
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ hℓ) h1
  choose w hw using hw
  have hX' : X = ∑ i, (w i : ℚ) • integralBasis K i := by
    conv_lhs => rw [← (integralBasis K).sum_repr X]
    simp only [hw]
  rw [hX']
  refine IsIntegral.sum _ fun i _ => ?_
  rw [Rat.smul_def, Rat.cast_intCast, integralBasis_apply]
  have hwi : IsIntegral ℤ ((w i : ℤ) : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := w i))
  exact hwi.mul (RingOfIntegers.isIntegral_coe _)

end PI.TrDualLocW
