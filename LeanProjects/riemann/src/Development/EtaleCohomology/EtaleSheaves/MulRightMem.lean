import Development.EtaleCohomology.EtaleSheaves.NoetherianLocalChartOverlapFiniteComplement

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemPowProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mul_left_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : s * y ∈ I • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr (S.mul_mem hs hn)
  · rw [mul_add]; exact add_mem hx hy

theorem mul_right_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : y * s ∈ I • Subalgebra.toSubmodule S := by
  rw [mul_comm]; exact mul_left_mem S I hs hy

theorem mul_mem_mul (S : Subalgebra A K) (I J : Ideal A) {x y : K}
    (hx : x ∈ I • Subalgebra.toSubmodule S) (hy : y ∈ J • Subalgebra.toSubmodule S) :
    x * y ∈ (I * J) • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun a b ha hb => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_left_mem S J hn hy)
  · rw [add_mul]; exact add_mem ha hb

theorem lift_pow (S : Subalgebra A K) (x : K) (hx : x ∈ S) (hp : x * x - x ∈ mS S) (n : ℕ) :
    ∃ y ∈ S, y - x ∈ mS S ∧
      y * y - y ∈ (IsLocalRing.maximalIdeal A ^ (2 ^ n)) • Subalgebra.toSubmodule S := by
  induction n with
  | zero => exact ⟨x, hx, by simp, by simpa [mS] using hp⟩
  | succ n ih =>
    obtain ⟨y, hy, hyx, hyy⟩ := ih
    have hle : IsLocalRing.maximalIdeal A ^ (2 ^ n) ≤ IsLocalRing.maximalIdeal A :=
      Ideal.pow_le_self (by positivity)
    have h2y : y + y - 1 ∈ S := S.sub_mem (S.add_mem hy hy) S.one_mem
    have hpS : y * y - y ∈ S := S.sub_mem (S.mul_mem hy hy) hy
    refine ⟨y - (y + y - 1) * (y * y - y), S.sub_mem hy (S.mul_mem h2y hpS), ?_, ?_⟩
    · rw [show y - (y + y - 1) * (y * y - y) - x = (y - x) - (y + y - 1) * (y * y - y) by ring]
      exact sub_mem hyx (Submodule.smul_mono_left hle (mul_left_mem S _ h2y hyy))
    · have h4 : (y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - 1 - 1 - 1 ∈ S :=
        S.sub_mem (S.sub_mem (S.sub_mem (S.add_mem (S.add_mem (S.add_mem hpS hpS) hpS) hpS)
          S.one_mem) S.one_mem) S.one_mem
      have hsq := mul_mem_mul S _ _ hyy hyy
      rw [← pow_add, ← two_mul, ← pow_succ'] at hsq
      have := mul_right_mem S _ h4 hsq
      convert this using 1
      ring

theorem LZIdemPow_of : LateralTheory.E.LZIdemSumNoetherian.LZIdemPow := by
  intro A _ _ K _ _ B C t hc e f hp k
  obtain ⟨he, hf, hee, hff, hef⟩ := hp
  obtain ⟨b, hb, hbe, hbb⟩ := lift_pow B e he hee (k + 1)
  obtain ⟨c, hcC, hcf, hcc⟩ := lift_pow C f hf hff (k + 1)
  have hBD : B ≤ AdjoinInv B t := fun x hx => Algebra.subset_adjoin (Or.inl hx)
  have hCD : C ≤ AdjoinInv B t := by
    intro x hx; rw [hc.glue]; exact Algebra.subset_adjoin (Or.inl hx)
  have hbD : b ∈ AdjoinInv B t := hBD hb
  have hcD : c ∈ AdjoinInv B t := hCD hcC
  have hmono : ∀ (I : Ideal A) (S : Subalgebra A K), S ≤ AdjoinInv B t → ∀ x,
      x ∈ I • Subalgebra.toSubmodule S → x ∈ I • Subalgebra.toSubmodule (AdjoinInv B t) :=
    fun I S h x hx => Submodule.smul_mono (le_refl I) (fun y hy => h hy) hx
  have hpow : IsLocalRing.maximalIdeal A ^ (2 ^ (k + 1)) ≤ IsLocalRing.maximalIdeal A ^ (k + 1) :=
    Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le
  have hp : b * b - b ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ B hBD _ hbb)
  have hq : c * c - c ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ C hCD _ hcc)
  have hd1 : b - c ∈ (IsLocalRing.maximalIdeal A ^ 1) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [pow_one, show b - c = (b - e) + (e - f) - (c - f) by ring]
    exact sub_mem (add_mem (hmono _ B hBD _ hbe) hef) (hmono _ C hCD _ hcf)
  have hcube : (b - c) * (b - c) * (b - c) - (b - c) ∈
      (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [show (b - c) * (b - c) * (b - c) - (b - c) = (b * b - b) - (c * c - c) - (c + c) * (b * b - b)
      + (b + b) * (c * c - c) + (b - c) * (b * b - b) + (b - c) * (c * c - c) by ring]
    have hbc : b - c ∈ AdjoinInv B t := (AdjoinInv B t).sub_mem hbD hcD
    refine add_mem (add_mem (add_mem (sub_mem (sub_mem hp hq) ?_) ?_) ?_) ?_
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hcD hcD) hp
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hbD hbD) hq
    · exact mul_left_mem _ _ hbc hp
    · exact mul_left_mem _ _ hbc hq
  have key : ∀ j, j + 1 ≤ k + 1 →
      b - c ∈ (IsLocalRing.maximalIdeal A ^ (j + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    intro j
    induction j with
    | zero => intro _; simpa using hd1
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h3 := mul_mem_mul _ _ _ (mul_mem_mul _ _ _ h1 h1) h1
      rw [← pow_add, ← pow_add] at h3
      have h3' := Submodule.smul_mono_left (Ideal.pow_le_pow_right (show j + 1 + 1 ≤ j + 1 + (j + 1) + (j + 1) by omega)) h3
      have hc' := Submodule.smul_mono_left (Ideal.pow_le_pow_right hj) hcube
      rw [show b - c = (b - c) * (b - c) * (b - c) - ((b - c) * (b - c) * (b - c) - (b - c)) by ring]
      exact sub_mem h3' hc'
  refine ⟨b, hb, c, hcC, ?_, hcf, ?_⟩
  · rw [← neg_sub]; exact neg_mem hbe
  · exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (key k le_rfl)

end LateralTheory.E.LZIdemPowProof
