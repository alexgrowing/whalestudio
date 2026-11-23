import Mathlib

namespace GlobalTheory

theorem parallelogram_zsmul {E : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (k : ℤ) (f : E) :
    Q (k • f) = k ^ 2 * Q f := by
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have hneg : ∀ g, Q (-g) = Q g := by
    intro g
    have := hQ 0 g
    simp only [zero_add, zero_sub, h0] at this
    omega
  have hnat : ∀ n : ℕ, Q ((n : ℤ) • f) = (n : ℤ) ^ 2 * Q f ∧
      Q (((n : ℤ) + 1) • f) = ((n : ℤ) + 1) ^ 2 * Q f := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have h := hQ (((n : ℤ) + 1) • f) f
      have e1 : ((n : ℤ) + 1) • f + f = (((n + 1 : ℕ) : ℤ) + 1) • f := by
        push_cast; module
      have e2 : ((n : ℤ) + 1) • f - f = (n : ℤ) • f := by module
      rw [e1, e2, ih.1, ih.2] at h
      push_cast at h ⊢
      linear_combination h
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact (hnat n).1
  · rw [neg_smul, hneg, (hnat n).1]; ring

theorem parallelogram_sum_le {E ι : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (hpos : ∀ f, 0 ≤ Q f)
    (u : ι → E) (s : Finset ι) :
    ∃ C : ℕ, ∀ (z : ι → ℤ) (M : ℤ), (∀ i, |z i| ≤ M) →
      Q (∑ i ∈ s, z i • u i) ≤ C * M ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, fun z M _ => ?_⟩
    have := parallelogram_zsmul Q hQ 0 0
    simp at this
    simp [this]
  | insert a s ha ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨2 * (Q (u a)).toNat + 2 * C, fun z M hz => ?_⟩
    rw [Finset.sum_insert ha]
    have h1 := hQ (z a • u a) (∑ i ∈ s, z i • u i)
    have h2 := hpos (z a • u a - ∑ i ∈ s, z i • u i)
    have h3 := hC z M hz
    have h4 := parallelogram_zsmul Q hQ (z a) (u a)
    have h5 : z a ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (z a)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hz a) 2
    have h6 := mul_le_mul_of_nonneg_right h5 (hpos (u a))
    push_cast
    rw [Int.toNat_of_nonneg (hpos (u a))]
    nlinarith

theorem exists_dvd_coords_of_definite_form :
    ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  intro E _ H Q hQ hpos hdef n u hu hli
  obtain ⟨C, hC⟩ := parallelogram_sum_le Q hQ hpos u Finset.univ
  rw [Fintype.linearIndependent_iff] at hli
  set R : ℕ := C + 1 with hR
  refine ⟨(R ^ n).factorial, Nat.factorial_pos _, fun k m h hh hk => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · intro i
    have := hli m (by simpa using hk.symm) i
    simp [this]
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hR0 : (0 : ℤ) < R := by positivity
  obtain ⟨a, ha, b, hb, hab, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (R ^ n + 1))
    (t := Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) R))
    (f := fun (j : ℕ) (i : Fin n) => ((R : ℤ) * (((j : ℤ) * m i) % k)) / k)
    (by simp [Fintype.card_piFinset])
    (by
      intro j _
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]
      intro i
      have h1 := Int.emod_nonneg ((j : ℤ) * m i) hk0.ne'
      have h2 := Int.emod_lt_of_pos ((j : ℤ) * m i) hk0
      refine ⟨Int.ediv_nonneg (by positivity) hk0.le, ?_⟩
      apply Int.ediv_lt_of_lt_mul hk0
      exact mul_lt_mul_of_pos_left h2 hR0)
  set y : Fin n → ℤ := fun i => ((a : ℤ) * m i) % k - ((b : ℤ) * m i) % k with hy
  set q : Fin n → ℤ := fun i => ((a : ℤ) * m i) / k - ((b : ℤ) * m i) / k with hq
  have hyq : ∀ i, y i = ((a : ℤ) - b) * m i - k * q i := by
    intro i
    simp only [hy, hq, Int.emod_def]
    ring
  have hbound : ∀ i, |(R : ℤ) * y i| ≤ k := by
    intro i
    have e := congrFun hf i
    beta_reduce at e
    have a1 := Int.emod_nonneg ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0.ne'
    have a2 := Int.emod_lt_of_pos ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0
    have b1 := Int.emod_nonneg ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0.ne'
    have b2 := Int.emod_lt_of_pos ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0
    rw [Int.emod_def] at a1 a2 b1 b2
    rw [e] at a1 a2
    simp only [hy]
    rw [abs_le, mul_sub]
    constructor <;> linarith
  set w : E := ((a : ℤ) - b) • h - ∑ i, q i • u i with hw
  have hwH : w ∈ H := H.sub_mem (H.zsmul_mem hh _) (H.sum_mem fun i _ => H.zsmul_mem (hu i) _)
  have hkw : (k : ℤ) • w = ∑ i, y i • u i := by
    rw [hw, smul_sub, smul_comm, natCast_zsmul h k, hk, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyq i, smul_smul, smul_smul, sub_smul]
  have hRkw : ((R : ℤ) * k) • w = ∑ i, ((R : ℤ) * y i) • u i := by
    rw [mul_smul, hkw, Finset.smul_sum]
    simp only [smul_smul]
  have hle := hC (fun i => (R : ℤ) * y i) k hbound
  rw [← hRkw, parallelogram_zsmul Q hQ] at hle
  have hQw : Q w = 0 := by
    by_contra hne
    have h1 : 1 ≤ Q w := by have := hpos w; omega
    have h2 : ((R : ℤ) * k) ^ 2 ≤ ((R : ℤ) * k) ^ 2 * Q w := le_mul_of_one_le_right (by positivity) h1
    have h3 : (C : ℤ) < (R : ℤ) ^ 2 := by
      rw [hR]; push_cast; nlinarith [Int.natCast_nonneg C]
    have h4 := mul_lt_mul_of_pos_right h3 (show (0 : ℤ) < (k : ℤ) ^ 2 by positivity)
    rw [mul_pow] at h2 hle
    linarith
  have hw0 := hdef w hwH hQw
  rw [hw0, smul_zero] at hkw
  intro i
  have hyi := hli y hkw.symm i
  have hd : (k : ℤ) ∣ ((a : ℤ) - b) * m i := ⟨q i, by have := hyq i; linarith⟩
  refine hd.trans (mul_dvd_mul_right ?_ _)
  rw [← Int.natAbs_dvd, Int.natCast_dvd_natCast]
  rw [Finset.mem_range] at ha hb
  apply Nat.dvd_factorial
  · omega
  · omega

end GlobalTheory
