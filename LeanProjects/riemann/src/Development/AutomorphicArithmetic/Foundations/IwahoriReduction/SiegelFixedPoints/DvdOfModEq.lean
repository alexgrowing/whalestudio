import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L

section Series

variable {K : Type} [Field K] [CharZero K]

end Series

section Root

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω]

end Root

end UpperTheory.Kd.L

private theorem eps_eOm_eq_cexp {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) := by
  unfold eOm
  apply Function.invFun_eq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast x.den_nz⟩
  haveI : NeZero x.den := ⟨x.den_nz⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have h2 := hξ.map_of_injective ε.injective
  have h1 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    linear_combination (2 * ↑Real.pi * Complex.I) * hx
  obtain ⟨i, -, hi⟩ := h2.eq_pow_of_pow_eq_one h1
  exact ⟨ξ ^ i, by rw [map_pow, hi]⟩

private theorem eOm_inv_mul_pow_eq_eOm_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (D M : ℕ) (hD : 0 < D) :
    eOm ε (1 / ((D * M : ℕ) : ℚ)) ^ D = eOm ε (1 / (M : ℚ)) := by
  apply ε.injective
  rw [map_pow, eps_eOm_eq_cexp, eps_eOm_eq_cexp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  have : (D:ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  by_cases hM : (M:ℂ) = 0
  · simp [hM]
  · field_simp

private theorem eisF_mul_scale_eq_ite_dvd {K : Type*} [Field K] (D M : ℕ) (ζ' ζ : K) (hζ : ζ' ^ D = ζ) (A a : ℤ) (hD : 0 < D) (hA : ¬ (M:ℤ) ∣ A) (n : ℕ) :
    eisF 1 (D * M) ζ' ((D:ℤ) * A) ((D:ℤ) * a) n = if D ∣ n then eisF 1 M ζ A a (n / D) else 0 := by
  have hD' : (D:ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x : ℤ, x ≡ (D:ℤ) * A [ZMOD ((D * M : ℕ) : ℤ)] → (D:ℤ) ∣ x := by
    intro x hx
    have h := hx.symm.dvd
    push_cast at h
    have h2 : (D:ℤ) ∣ x - D * A := (Dvd.intro _ rfl).trans h
    have h3 : (D:ℤ) ∣ D * A := Dvd.intro _ rfl
    simpa using h2.add h3
  have cong : ∀ y : ℤ, (((D:ℤ) * y) ≡ (D:ℤ) * A [ZMOD ((D * M : ℕ) : ℤ)] ↔ y ≡ A [ZMOD M]) := by
    intro y
    push_cast
    exact ⟨Int.ModEq.mul_left_cancel' hD', fun h => Int.ModEq.mul_left' h⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [eisF, const0, if_true, dvd_zero, Nat.zero_div]
    have h1 : ¬ ((D * M : ℕ) : ℤ) ∣ (D:ℤ) * A := by
      push_cast
      rwa [mul_dvd_mul_iff_left hD']
    rw [if_neg h1, if_neg hA]
    unfold frc
    push_cast
    rw [Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hD)]
    push_cast
    have : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  · simp only [eisF, coefPos, hn.ne', if_false, Nat.sub_self, pow_zero, one_mul]
    by_cases hDn : D ∣ n
    · rw [if_pos hDn]
      obtain ⟨k, rfl⟩ := hDn
      have hk : k ≠ 0 := by
        rintro rfl
        simp at hn
      rw [Nat.mul_div_cancel_left k hD, if_neg hk]
      have hsub : k.divisors ⊆ (D * k).divisors :=
        Nat.divisors_subset_of_dvd (Nat.mul_ne_zero hD.ne' hk) (dvd_mul_left k D)
      have hpow : ∀ t : ℤ, ζ' ^ ((D:ℤ) * t) = ζ ^ t := by
        intro t
        rw [zpow_mul, zpow_natCast, hζ]
      have hout : ∀ x : ℕ, x ∣ D * k → (D:ℤ) ∣ ((D * k / x : ℕ) : ℤ) → x ∣ k := by
        intro x hx hdx
        rw [Int.natCast_dvd_natCast] at hdx
        obtain ⟨e, he⟩ := hdx
        have h1 : D * k / x * x = D * k := Nat.div_mul_cancel hx
        rw [he, mul_assoc] at h1
        exact ⟨e, by rw [mul_comm x e]; exact (Nat.eq_of_mul_eq_mul_left hD h1).symm⟩
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl
        intro x hx
        have hxk : x ∣ k := Nat.dvd_of_mem_divisors hx
        have e1 : ((D * k / x : ℕ) : ℤ) = (D:ℤ) * ((k / x : ℕ) : ℤ) := by
          rw [Nat.mul_div_assoc D hxk]
          push_cast
          ring
        simp only [e1, neg_mul_eq_mul_neg, cong, mul_assoc, hpow]
      · intro x hx hxn
        have hx' : x ∣ D * k := Nat.dvd_of_mem_divisors hx
        have hnot : ¬ x ∣ k := fun h => hxn (Nat.mem_divisors.mpr ⟨h, hk⟩)
        rw [if_neg, if_neg, sub_zero]
        · intro h
          exact hnot (hout x hx' (by simpa using key _ h))
        · intro h
          exact hnot (hout x hx' (key _ h))
    · rw [if_neg hDn]
      apply Finset.sum_eq_zero
      intro x hx
      have hx' : x ∣ n := Nat.dvd_of_mem_divisors hx
      have hout : (D:ℤ) ∣ ((n / x : ℕ) : ℤ) → False := by
        intro hdx
        rw [Int.natCast_dvd_natCast] at hdx
        exact hDn (hdx.trans (Nat.div_dvd_of_dvd hx'))
      rw [if_neg, if_neg, sub_zero]
      · intro h
        exact hout (by simpa using key _ h)
      · intro h
        exact hout (key _ h)

private theorem smF_mul_scale_eq_ite_dvd {K : Type*} [Field K] (c : ℤ) (D M : ℕ) (ζ' ζ : K) (hζ : ζ' ^ D = ζ) (A a : ℤ) (hD : 0 < D) (hA : ¬ (M:ℤ) ∣ A) (hcA : ¬ (M:ℤ) ∣ c * A) (n : ℕ) :
    smF c 1 (D * M) ζ' ((D:ℤ) * A) ((D:ℤ) * a) n = if D ∣ n then smF c 1 M ζ A a (n / D) else 0 := by
  unfold smF
  rw [mul_left_comm c (D:ℤ) A, mul_left_comm c (D:ℤ) a, eisF_mul_scale_eq_ite_dvd D M ζ' ζ hζ A a hD hA, eisF_mul_scale_eq_ite_dvd D M ζ' ζ hζ (c * A) (c * a) hD hcA]
  split_ifs <;> simp

private theorem cmul_dilate_eq_ite_dvd {K : Type*} [Field K] (D : ℕ) (hD : 0 < D) (f g f' g' : ℕ → K) (hf : ∀ n, f' n = if D ∣ n then f (n / D) else 0) (hg : ∀ n, g' n = if D ∣ n then g (n / D) else 0) (N : ℕ) :
    cmul f' g' N = if D ∣ N then cmul f g (N / D) else 0 := by
  unfold cmul
  by_cases hN : D ∣ N
  · rw [if_pos hN]
    obtain ⟨K0, rfl⟩ := hN
    rw [Nat.mul_div_cancel_left K0 hD]
    have hsub : (Finset.range (K0 + 1)).image (fun k => D * k) ⊆ Finset.range (D * K0 + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
      obtain ⟨k, hk, rfl⟩ := hi
      have := Nat.mul_le_mul_left D (Nat.lt_succ_iff.mp hk)
      omega
    rw [← Finset.sum_subset hsub, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      have e : D * K0 - D * k = D * (K0 - k) := (Nat.mul_sub D K0 k).symm
      rw [hf, hg, if_pos (dvd_mul_right D k), e, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hD, Nat.mul_div_cancel_left _ hD]
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hD hxy
    · intro i hi hni
      rw [hf]
      split_ifs with hDi
      · exfalso
        obtain ⟨k, rfl⟩ := hDi
        apply hni
        simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
        refine ⟨k, ?_, rfl⟩
        have h1 : D * k ≤ D * K0 := by omega
        have := Nat.le_of_mul_le_mul_left h1 hD
        omega
      · simp
  · rw [if_neg hN]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hf, hg]
    split_ifs with h1 h2
    · exfalso
      apply hN
      have := Nat.dvd_add h1 h2
      rwa [Nat.add_sub_cancel' hi'] at this
    · simp
    · simp
    · simp

private theorem coefQ_eq_of_mul_eq_nat {Ω : Type} [Field Ω] (L : ℕ) (hL : 0 < L) (F : ℕ → Ω) (r : ℚ) (N : ℕ) (h : r * L = N) :
    coefQ L F r = F N := by
  unfold coefQ
  have hL' : (0:ℚ) < L := by exact_mod_cast hL
  have hr : 0 ≤ r := by
    have h0 : 0 ≤ r * L := by
      rw [h]
      exact Nat.cast_nonneg _
    exact (mul_nonneg_iff_of_pos_right hL').mp h0
  rw [if_pos ⟨hr, by rw [h]; simp⟩, h]
  simp

private theorem coefQ_eq_zero_of_not_nat {Ω : Type} [Field Ω] (L : ℕ) (F : ℕ → Ω) (r : ℚ) (h : ¬ ∃ N : ℕ, r * L = N) :
    coefQ L F r = 0 := by
  unfold coefQ
  rw [if_neg]
  rintro ⟨hr, hd⟩
  apply h
  have h1 : ((r * L).num : ℚ) = r * L := Rat.coe_int_num_of_den_eq_one hd
  have h2 : 0 ≤ (r * L).num := Rat.num_nonneg.mpr (mul_nonneg hr (Nat.cast_nonneg _))
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h2
  refine ⟨m, ?_⟩
  rw [← h1, hm]
  simp

theorem UpperTheory.Kd.L.resc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (D M c d L : ℕ) (A a B b : ℤ), 0 < D → 0 < M → 0 < L → ¬ (M : ℤ) ∣ A → ¬ (M : ℤ) ∣ c * A → ¬ (M : ℤ) ∣ B → ¬ (M : ℤ) ∣ d * B → ∀ r : ℚ, coefQ L (cmul (smF c 1 (D * M) (eOm ε (1 / ((D * M : ℕ) : ℚ))) (D * A) (D * a)) (smF d 1 (D * M) (eOm ε (1 / ((D * M : ℕ) : ℚ))) (D * B) (D * b))) r = coefQ L (cmul (smF c 1 M (eOm ε (1 / (M : ℚ))) A a) (smF d 1 M (eOm ε (1 / (M : ℚ))) B b)) (r / D) := by
  intro Ω _ _ _ _ ε D M c d L A a B b hD hM hL hA hcA hB hdB r
  have hζ := eOm_inv_mul_pow_eq_eOm_inv ε D M hD
  have h1 := smF_mul_scale_eq_ite_dvd (c:ℤ) D M _ _ hζ A a hD hA hcA
  have h2 := smF_mul_scale_eq_ite_dvd (d:ℤ) D M _ _ hζ B b hD hB hdB
  have hc := cmul_dilate_eq_ite_dvd D hD _ _ _ _ h1 h2
  by_cases h : ∃ N : ℕ, r * L = N
  · obtain ⟨N, hN⟩ := h
    rw [coefQ_eq_of_mul_eq_nat L hL _ r N hN, hc]
    by_cases hDN : D ∣ N
    · obtain ⟨K0, rfl⟩ := hDN
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hD]
      refine (coefQ_eq_of_mul_eq_nat L hL _ _ K0 ?_).symm
      have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      rw [div_mul_eq_mul_div, hN]
      push_cast
      field_simp
    · rw [if_neg hDN, coefQ_eq_zero_of_not_nat]
      rintro ⟨m, hm⟩
      apply hDN
      refine ⟨m, ?_⟩
      have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      have e : (N:ℚ) = D * m := by
        rw [← hN, ← hm]
        field_simp
      exact_mod_cast e
  · rw [coefQ_eq_zero_of_not_nat L _ r h, coefQ_eq_zero_of_not_nat]
    rintro ⟨m, hm⟩
    apply h
    refine ⟨D * m, ?_⟩
    have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    rw [← hm]
    field_simp
