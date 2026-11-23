import Mathlib

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.invMem :
    ∀ (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (S : Subalgebra Λ (Module.End Λ M)) (u : (Module.End Λ M)ˣ), (u : Module.End Λ M) ∈ S → ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ∈ S := by
  intro Λ M _ _ _ _ S u hu
  obtain ⟨p, hp, hpv⟩ :=
    LinearMap.exists_monic_and_aeval_eq_zero Λ ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M)
  have key : ∀ n i, i ≤ n → (u : Module.End Λ M) ^ n *
      ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i = (u : Module.End Λ M) ^ (n - i) := by
    intro n i hi
    have h1 : (u : Module.End Λ M) ^ i * ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv]
    rw [← pow_sub_mul_pow (u : Module.End Λ M) hi, mul_assoc, h1, mul_one]
  rw [Polynomial.aeval_eq_sum_range] at hpv
  cases h : p.natDegree with
  | zero =>
    have hc : p.coeff 0 = 1 := by rw [← h]; exact hp.coeff_natDegree
    rw [h, Finset.sum_range_one, hc, one_smul, pow_zero] at hpv
    have hz : ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) = 0 := by
      rw [← mul_one ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M), hpv, mul_zero]
    rw [hz]
    exact S.zero_mem
  | succ n =>
    have hc : p.coeff (n + 1) = 1 := by rw [← h]; exact hp.coeff_natDegree
    rw [h, Finset.sum_range_succ, hc, one_smul] at hpv
    have hmul := congrArg (fun w => (u : Module.End Λ M) ^ n * w) hpv
    rw [mul_add, Finset.mul_sum, mul_zero] at hmul
    have hlast : (u : Module.End Λ M) ^ n *
        ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ (n + 1) =
        ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) := by
      rw [pow_succ, ← mul_assoc, key n n le_rfl, Nat.sub_self, pow_zero, one_mul]
    rw [hlast] at hmul
    have hterm : ∀ i ∈ Finset.range (n + 1), (u : Module.End Λ M) ^ n *
        (p.coeff i • ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i) =
        p.coeff i • (u : Module.End Λ M) ^ (n - i) := by
      intro i hi
      rw [mul_smul_comm, key n i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    rw [Finset.sum_congr rfl hterm] at hmul
    rw [eq_neg_of_add_eq_zero_right hmul]
    exact S.neg_mem (S.sum_mem fun i _ => S.smul_mem (S.pow_mem hu _) _)
