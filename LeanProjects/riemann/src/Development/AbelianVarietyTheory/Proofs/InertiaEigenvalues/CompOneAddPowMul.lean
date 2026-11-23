import Mathlib

open scoped LaurentSeries PowerSeries

namespace GlobalTheory.PsiBasis

variable {k : Type} [Field k]

noncomputable def comp (l : ℕ) (hl : 0 < l) (i : ℕ) : k⸨X⸩ →ₗ[k] k⸨X⸩ where
  toFun y :=
    { coeff := fun m => y.coeff (l * m + i)
      isPWO_support' := by
        apply Set.IsWF.isPWO
        apply BddBelow.isWF
        refine ⟨min 0 (y.order - i), fun m hm => ?_⟩
        by_contra h
        apply hm
        apply HahnSeries.coeff_eq_zero_of_lt_order
        have h1 : m < 0 := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
        have h2 : m < y.order - i := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
        have h3 : (1 : ℤ) ≤ l := by exact_mod_cast hl
        nlinarith }
  map_add' x y := by ext m; simp
  map_smul' c x := by ext m; simp

theorem comp_coeff (l : ℕ) (hl : 0 < l) (i : ℕ) (y : k⸨X⸩) (m : ℤ) :
    (comp l hl i y).coeff m = y.coeff (l * m + i) := rfl

theorem p_zpow (s : ℤ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single s 1 := by
  cases s with
  | ofNat n => simp [HahnSeries.single_pow]
  | negSucc n =>
    rw [zpow_negSucc, HahnSeries.single_pow, HahnSeries.inv_single]
    simp [Int.negSucc_eq]

theorem p_pow (s : ℕ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single (s : ℤ) 1 := by
  simp [HahnSeries.single_pow]

theorem mem_iff (s : ℤ) (x : k⸨X⸩) :
    (∃ b : k⟦X⟧, x = (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s * (b : k⸨X⸩)) ↔
      ∀ m < s, x.coeff m = 0 := by
  rw [p_zpow]
  constructor
  · rintro ⟨b, rfl⟩ m hm
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, if_pos (by omega), mul_zero]
  · intro h
    refine ⟨PowerSeries.mk fun n => x.coeff (s + n), ?_⟩
    ext m
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, one_mul]
    split_ifs with hm
    · exact h m (by omega)
    · rw [PowerSeries.coeff_mk]; congr 1; omega

section
variable (l : ℕ) (hl : 0 < l) (φ : k⸨X⸩ →+* k⸨X⸩)
  (hφ : ∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0)
include hl hφ

theorem comp_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ j * φ a)
      = if j = i then a else 0 := by
  ext m
  have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [comp_coeff, p_pow, HahnSeries.coeff_single_mul, one_mul, hφ]
  by_cases h : j = i
  · subst h
    simp [Int.mul_ediv_cancel_left _ hl']
  · rw [if_neg h, if_neg]
    · simp
    · intro hd
      have : (l : ℤ) ∣ (i : ℤ) - j := by
        have h2 := dvd_sub hd (dvd_mul_right (l : ℤ) m)
        have e : (l : ℤ) * m + i - j - l * m = i - j := by ring
        rwa [e] at h2
      have := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> omega)
      omega

theorem eq_of_comp_eq {y z : k⸨X⸩} (h : ∀ i < l, comp l hl i y = comp l hl i z) : y = z := by
  ext m
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  have h0 := Int.emod_nonneg m hl'.ne'
  have h1 := Int.emod_lt_of_pos m hl'
  have := congrArg (fun w => w.coeff (m / l)) (h (m % l).toNat (by omega))
  simp only [comp_coeff] at this
  rw [Int.toNat_of_nonneg h0, Int.mul_ediv_add_emod] at this
  exact this

theorem comp_one_add_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j * φ a)
      = (j.choose i) • a := by
  rw [add_comm, add_pow, Finset.sum_mul, map_sum]
  have : ∀ m ∈ Finset.range (j + 1),
      comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ m * 1 ^ (j - m) *
        (j.choose m : k⸨X⸩) * φ a) = if m = i then (j.choose i) • a else 0 := by
    intro m hm
    have hm' : m < l := by have := Finset.mem_range.1 hm; omega
    rw [one_pow, mul_one, mul_assoc, ← map_natCast φ, ← map_mul,
      comp_pow_mul l hl φ hφ hi hm']
    split_ifs with h
    · subst h; rw [nsmul_eq_mul]
    · rfl
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using h), zero_smul]

theorem existsUnique_decomp (y : k⸨X⸩) :
    ∃! x : Fin l → k⸨X⸩, y = ∑ j : Fin l,
      (1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j.val * φ (x j) := by
  let M : Matrix (Fin l) (Fin l) k⸨X⸩ := fun i j => (j.val.choose i.val : k⸨X⸩)
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular]
    · simp [M]
    · intro i j hij
      have : j.val < i.val := hij
      simp [M, Nat.choose_eq_zero_of_lt this]
  have hb : Function.Bijective M.mulVec :=
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hM, Matrix.mulVec_surjective_iff_isUnit.2 hM⟩
  have key : ∀ (x : Fin l → k⸨X⸩) (i : Fin l), comp l hl i (∑ j : Fin l,
      (1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j.val * φ (x j)) = M.mulVec x i := by
    intro x i
    rw [map_sum, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [comp_one_add_pow_mul l hl φ hφ i.2 j.2, nsmul_eq_mul]
  have := hb.existsUnique (fun i : Fin l => comp l hl i y)
  refine (existsUnique_congr fun x => ?_).1 this
  constructor
  · intro h
    refine eq_of_comp_eq l hl φ hφ fun i hi => ?_
    rw [key x ⟨i, hi⟩, h]
  · intro h
    funext i
    rw [← key, ← h]

end

noncomputable def psi (l : ℕ) (hl : 0 < l) : k⸨X⸩ →ₗ[k] k⸨X⸩ :=
  ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i

theorem psi_apply (l : ℕ) (hl : 0 < l) (y : k⸨X⸩) :
    psi l hl y = ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i y := by
  simp only [psi, LinearMap.sum_apply, LinearMap.smul_apply]

theorem finiteRing_sq_sub_mul_sq_eq_of_card : ∀ {k : Type} [Field k] (l : ℕ) (_ : 0 < l) (φ : k⸨X⸩ →+* k⸨X⸩), (∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0) → let p : k⸨X⸩ := HahnSeries.single 1 1; (∀ y : k⸨X⸩, ∃! x : Fin l → k⸨X⸩, y = ∑ j : Fin l, (1 + p) ^ j.val * φ (x j)) ∧ ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, (∀ a, ψ (φ a) = a) ∧ (∀ (a) (j : ℕ), 0 < j → j < l → ψ ((1 + p) ^ j * φ a) = 0) ∧ ∀ s : ℤ, ψ '' {x | ∃ b : k⟦X⟧, x = p ^ s * (b : k⸨X⸩)} = {x | ∃ b : k⟦X⟧, x = p ^ (s / l) * (b : k⸨X⸩)} := by
  intro k _ l hl φ hφ p
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  have hpow : ∀ j < l, ∀ a, psi l hl (p ^ j * φ a) = ((-1 : ℤ) ^ j) • a := by
    intro j hj a
    rw [psi_apply, Finset.sum_eq_single j]
    · congr 1
      exact (comp_pow_mul l hl φ hφ hj hj a).trans (if_pos rfl)
    · intro i hi hij
      have := (comp_pow_mul l hl φ hφ (Finset.mem_range.1 hi) hj a).trans (if_neg hij.symm)
      rw [this, smul_zero]
    · intro h; exact absurd (Finset.mem_range.2 hj) h
  refine ⟨existsUnique_decomp l hl φ hφ, psi l hl, fun a => ?_, fun a j hj0 hj => ?_, fun s => ?_⟩
  · simpa using hpow 0 hl a
  · rw [psi_apply]
    have : ∀ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i ((1 + p) ^ j * φ a)
        = ((-1 : ℤ) ^ i * (j.choose i : ℤ)) • a := by
      intro i hi
      have := comp_one_add_pow_mul l hl φ hφ (Finset.mem_range.1 hi) hj a
      rw [this]
      rw [mul_smul, natCast_zsmul]
    rw [Finset.sum_congr rfl this, ← Finset.sum_smul,
      ← Finset.sum_subset (Finset.range_subset_range.2 (show j + 1 ≤ l from hj)),
      Int.alternating_sum_range_choose_of_ne hj0.ne', zero_smul]
    intro i _ hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]
    simp
  · have h0 := Int.emod_nonneg s hl'.ne'
    have h1 := Int.emod_lt_of_pos s hl'
    have h2 := Int.mul_ediv_add_emod s l
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq, p, mem_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ m hm
      rw [psi_apply, HahnSeries.coeff_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : (i : ℤ) < l := by exact_mod_cast Finset.mem_range.1 hi
      have : (comp l hl i y).coeff m = 0 := by
        rw [comp_coeff]
        apply hy
        nlinarith
      rw [HahnSeries.coeff_smul, this, smul_zero]
    · intro hz
      refine ⟨p ^ (l - 1) * φ (((-1 : ℤ) ^ (l - 1)) • z), fun m hm => ?_, ?_⟩
      · rw [p_pow, HahnSeries.coeff_single_mul, one_mul, hφ]
        split_ifs with hd
        · obtain ⟨c, hc⟩ := hd
          rw [hc, Int.mul_ediv_cancel_left _ hl'.ne', HahnSeries.coeff_smul, hz, smul_zero]
          have : ((l - 1 : ℕ) : ℤ) = l - 1 := by omega
          rw [this] at hc
          nlinarith
        · rfl
      · rw [hpow _ (by omega), smul_smul, ← mul_pow]
        simp

theorem main : ∀ {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (φ : k⸨X⸩ →ₐ[k] k⸨X⸩), (∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0) → let p : k⸨X⸩ := HahnSeries.single 1 1; (∀ y : k⸨X⸩, ∃! x : Fin l → k⸨X⸩, y = ∑ j : Fin l, (1 + p) ^ j.val * φ (x j)) ∧ ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, (∀ a, ψ (φ a) = a) ∧ (∀ (a) (j : ℕ), 0 < j → j < l → ψ ((1 + p) ^ j * φ a) = 0) ∧ ∀ s : ℤ, ψ '' {x | ∃ b : k⟦X⟧, x = p ^ s * (b : k⸨X⸩)} = {x | ∃ b : k⟦X⟧, x = p ^ (s / l) * (b : k⸨X⸩)} :=
  fun l hp _ φ hφ => finiteRing_sq_sub_mul_sq_eq_of_card l hp.out.pos φ.toRingHom hφ

end GlobalTheory.PsiBasis
