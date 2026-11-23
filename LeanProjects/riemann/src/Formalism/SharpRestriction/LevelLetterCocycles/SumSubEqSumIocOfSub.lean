import Mathlib

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds

open Finset

variable (l : ℕ) [hl : Fact l.Prime]

theorem sum_Ioc_zero_eq_factorial (y : ℕ) :
    ∑ m ∈ Ioc 0 y, padicValNat l m = padicValNat l y.factorial := by
  induction y with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero n)]
    ring

theorem padicValNat_factorial_le_div_sub_one (y : ℕ) :
    ((padicValNat l y.factorial : ℕ) : ℝ) ≤ (y : ℝ) / ((l : ℝ) - 1) := by
  have h1 : 1 < l := hl.out.one_lt
  have hc : (0:ℝ) < (l:ℝ) - 1 := by
    have : (1:ℝ) < l := by exact_mod_cast h1
    linarith
  have key : (l - 1) * padicValNat l y.factorial ≤ y := by
    rw [sub_one_mul_padicValNat_factorial]; exact Nat.sub_le _ _
  have key' : (((l - 1 : ℕ) : ℝ)) * (padicValNat l y.factorial : ℝ) ≤ y := by
    exact_mod_cast key
  rw [Nat.cast_sub h1.le, Nat.cast_one] at key'
  rw [le_div_iff₀ hc]; linarith

theorem padicValNat_choose_le_logb' (k n : ℕ) :
    ((padicValNat l (k.choose n) : ℕ) : ℝ) ≤ Real.logb l k := by
  have h1 : padicValNat l (k.choose n) ≤ Nat.log l k := by
    rw [← Nat.factorization_def _ hl.out]
    exact Nat.factorization_choose_le_log
  have h2 : ((Nat.log l k : ℕ) : ℝ) ≤ Real.logb l k := by
    first
    | exact Real.natLog_le_logb k l
    | rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hl1 : (1:ℝ) < l := by exact_mod_cast hl.out.one_lt
        rw [Real.le_logb_iff_rpow_le hl1 (by exact_mod_cast hk), Real.rpow_natCast]
        exact_mod_cast Nat.pow_log_le_self l hk.ne'
  calc ((padicValNat l (k.choose n) : ℕ) : ℝ) ≤ ((Nat.log l k : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb l k := h2

theorem sum_Ioc_padicValNat_le_div_sub_one_add_logb (k0 k1 : ℕ) (h : k0 ≤ k1) :
    ((∑ m ∈ Ioc k0 k1, padicValNat l m : ℕ) : ℝ) ≤
      ((k1 - k0 : ℕ) : ℝ) / ((l : ℝ) - 1) + Real.logb l k1 := by
  have hsplit : ∑ m ∈ Ioc 0 k0, padicValNat l m + ∑ m ∈ Ioc k0 k1, padicValNat l m
      = ∑ m ∈ Ioc 0 k1, padicValNat l m :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le k0) h
  rw [sum_Ioc_zero_eq_factorial, sum_Ioc_zero_eq_factorial] at hsplit
  have hA : k1.choose k0 * k0.factorial ≠ 0 :=
    mul_ne_zero (Nat.choose_pos h).ne' (Nat.factorial_ne_zero k0)
  have hfac : k1.factorial = k1.choose k0 * k0.factorial * (k1 - k0).factorial :=
    (Nat.choose_mul_factorial_mul_factorial h).symm
  rw [hfac, padicValNat.mul hA (Nat.factorial_ne_zero _),
    padicValNat.mul (Nat.choose_pos h).ne' (Nat.factorial_ne_zero k0)] at hsplit
  have heq : ∑ m ∈ Ioc k0 k1, padicValNat l m
      = padicValNat l (k1.choose k0) + padicValNat l (k1 - k0).factorial := by omega
  rw [heq, Nat.cast_add]
  have h2 := padicValNat_factorial_le_div_sub_one l (k1 - k0)
  have h3 := padicValNat_choose_le_logb' l k1 k0
  linarith

theorem sum_sub_eq_sum_Ioc (j0 : ℤ) (k0 k1 : ℕ) (T : Finset ℤ)
    (hT : ∀ j, j ∈ T ↔ (k0 : ℤ) < j0 - j ∧ j0 - j ≤ k1) :
    ∑ j ∈ T, padicValInt l (j0 - j) = ∑ m ∈ Ioc k0 k1, padicValNat l m := by
  refine Finset.sum_nbij' (fun j => (j0 - j).toNat) (fun m => j0 - (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha
    simp only [padicValInt]
    congr 1
    omega

theorem sum_sub_eq_sum_Ioc_of_sub (j0 : ℤ) (k0 k1 : ℕ) (T : Finset ℤ)
    (hT : ∀ j, j ∈ T ↔ (k0 : ℤ) < j - j0 ∧ j - j0 ≤ k1) :
    ∑ j ∈ T, padicValInt l (j0 - j) = ∑ m ∈ Ioc k0 k1, padicValNat l m := by
  refine Finset.sum_nbij' (fun j => (j - j0).toNat) (fun m => j0 + (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha
    simp only [padicValInt]
    congr 1
    omega

theorem sum_erase_add_sum_le (a b S η h : ℕ) (hb : 2 * a + η ≤ b) (hbh : b ≤ h) (S₂ : Finset ℤ)
    (hS₂ : S₂ ⊆ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (j₀ : ℤ) (hj₀ : j₀ ∈ Icc ((b : ℤ) - a + 1) (b : ℤ)) :
    (((∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase j₀, padicValInt l (j₀ - j)) +
        ∑ j ∈ S₂, padicValInt l (j₀ - j) : ℕ) : ℝ) ≤
      (3 * (a : ℝ) + S + 2 * η - 1) / ((l : ℝ) - 1) + Real.logb l ((h + η : ℕ) : ℝ) := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hc : (0:ℝ) < (l:ℝ) - 1 := by linarith
  rw [Finset.mem_Icc] at hj₀
  obtain ⟨p, hp⟩ : ∃ p : ℕ, j₀ = (b : ℤ) - p := ⟨((b : ℤ) - j₀).toNat, by omega⟩
  subst hp
  have hpa : p + 1 ≤ a := by omega
  have e1 : ∑ j ∈ ((Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p)).filter
        (fun j => j < (b : ℤ) - p), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc
    intro j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have e2 : ∑ j ∈ ((Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p)).filter
        (fun j => ¬ j < (b : ℤ) - p), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 p, padicValNat l m := by
    apply sum_sub_eq_sum_Ioc_of_sub
    intro j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have e12 : ∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p),
        padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m + ∑ m ∈ Ioc 0 p, padicValNat l m := by
    rw [← e1, ← e2]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hdisj : Disjoint (Icc ((b : ℤ) + 1) ((b : ℤ) + S + a))
      (Icc (1 - (η : ℤ)) ((η : ℤ) + a)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    omega
  have e3 : ∑ j ∈ S₂, padicValInt l ((b : ℤ) - p - j) ≤
      ∑ j ∈ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a), padicValInt l ((b : ℤ) - p - j) +
      ∑ j ∈ Icc (1 - (η : ℤ)) ((η : ℤ) + a), padicValInt l ((b : ℤ) - p - j) := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset hS₂
  have eA : ∑ j ∈ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc p (p + S + a), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc_of_sub
    intro j
    rw [Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have eB : ∑ j ∈ Icc (1 - (η : ℤ)) ((η : ℤ) + a), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc
    intro j
    rw [Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have ePQ : ∑ m ∈ Ioc 0 p, padicValNat l m + ∑ m ∈ Ioc p (p + S + a), padicValNat l m
      = padicValNat l (p + S + a).factorial := by
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le p) (by omega : p ≤ p + S + a),
      sum_Ioc_zero_eq_factorial]
  have eR : ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m = padicValNat l (a - 1 - p).factorial :=
    sum_Ioc_zero_eq_factorial l _
  have hN : (∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p),
        padicValInt l ((b : ℤ) - p - j)) + ∑ j ∈ S₂, padicValInt l ((b : ℤ) - p - j)
      ≤ padicValNat l (a - 1 - p).factorial + padicValNat l (p + S + a).factorial +
        ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m := by
    rw [eA, eB] at e3
    rw [e12]
    omega
  have hR := padicValNat_factorial_le_div_sub_one l (a - 1 - p)
  have hP := padicValNat_factorial_le_div_sub_one l (p + S + a)
  have hB := sum_Ioc_padicValNat_le_div_sub_one_add_logb l (b - p - η - a - 1) (b - p + η - 1) (by omega)
  have hx : (0:ℝ) < ((b - p + η - 1 : ℕ) : ℝ) := by
    have : 0 < b - p + η - 1 := by omega
    exact_mod_cast this
  have hxy : ((b - p + η - 1 : ℕ) : ℝ) ≤ ((h + η : ℕ) : ℝ) := by
    exact_mod_cast (by omega : b - p + η - 1 ≤ h + η)
  have hlog : Real.logb l ((b - p + η - 1 : ℕ) : ℝ) ≤ Real.logb l ((h + η : ℕ) : ℝ) := by
    first
    | exact Real.logb_le_logb_of_le hl1 hx hxy
    | exact (Real.logb_le_logb hl1 hx (by linarith)).mpr hxy
  have hnum : ((a - 1 - p : ℕ) : ℝ) + ((p + S + a : ℕ) : ℝ) +
      (((b - p + η - 1) - (b - p - η - a - 1) : ℕ) : ℝ) = 3 * (a : ℝ) + S + 2 * η - 1 := by
    have e4 : (b - p + η - 1) - (b - p - η - a - 1) = 2 * η + a := by omega
    have e6 : ((a - 1 - p : ℕ) : ℝ) + 1 + p = a := by
      exact_mod_cast (by omega : a - 1 - p + 1 + p = a)
    rw [e4]
    push_cast
    linarith
  have hdiv : ((a - 1 - p : ℕ) : ℝ) / ((l : ℝ) - 1) + ((p + S + a : ℕ) : ℝ) / ((l : ℝ) - 1) +
      (((b - p + η - 1) - (b - p - η - a - 1) : ℕ) : ℝ) / ((l : ℝ) - 1)
      = (3 * (a : ℝ) + S + 2 * η - 1) / ((l : ℝ) - 1) := by
    rw [← hnum]; ring
  calc _ ≤ ((padicValNat l (a - 1 - p).factorial + padicValNat l (p + S + a).factorial +
          ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m : ℕ) : ℝ) :=
        Nat.cast_le.mpr hN
    _ = ((padicValNat l (a - 1 - p).factorial : ℕ) : ℝ) +
          ((padicValNat l (p + S + a).factorial : ℕ) : ℝ) +
          ((∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_add]
    _ ≤ _ := by linarith

end Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds
