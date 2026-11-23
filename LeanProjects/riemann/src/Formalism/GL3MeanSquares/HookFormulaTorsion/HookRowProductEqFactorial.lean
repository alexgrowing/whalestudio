import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.LogVandermondeProofs.GammaIntegralPolynomialBound

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

theorem third_zeta_injective : InjectiveReindexNormLe := by
  intro X X' V V' _ _ _ _ _ _ e P φ he
  calc ∑ x', ‖P (φ (e x'))‖ ^ 2 ≤ ∑ x', ‖P‖ ^ 2 * ‖φ (e x')‖ ^ 2 := by
        refine Finset.sum_le_sum fun x' _ => ?_
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm _) 2
    _ = ‖P‖ ^ 2 * ∑ x', ‖φ (e x')‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ‖P‖ ^ 2 * ∑ x, ‖φ x‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ x', ‖φ (e x')‖ ^ 2 = ∑ x ∈ (univ : Finset X').map ⟨e, he⟩, ‖φ x‖ ^ 2 := by
              rw [Finset.sum_map]; rfl
          _ ≤ ∑ x, ‖φ x‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun x _ _ => by positivity)

private lemma weyl_factor_bounds {n : ℕ} (lam : Fin (n + 1) → ℤ) (h : Antitone lam) (i j : Fin (n + 1))
    (hij : i < j) :
    1 ≤ (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) ∧
    (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
      ≤ (Wnum lam : ℝ) := by
  have hij' : ((i:ℕ):ℝ) + 1 ≤ ((j:ℕ):ℝ) := by exact_mod_cast hij
  have hd : (0:ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by linarith
  have h1 : (lam j : ℝ) ≤ lam i := by exact_mod_cast h hij.le
  have h2 : (lam i : ℝ) ≤ lam 0 := by exact_mod_cast h (Fin.zero_le i)
  have h3 : (lam (Fin.last n) : ℝ) ≤ lam j := by exact_mod_cast h (Fin.le_last j)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
  constructor
  · rw [le_div_iff₀ hd]; push_cast; linarith
  · rw [div_le_iff₀ hd]; unfold Wnum; push_cast
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (lam 0 : ℝ) - lam (Fin.last n))
      (by linarith : (0:ℝ) ≤ ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) - 1),
      mul_nonneg hn0 hd.le]

private lemma one_le_weyl_numerator {n : ℕ} (lam : Fin (n + 1) → ℤ) (h : Antitone lam) :
    (1:ℝ) ≤ (Wnum lam : ℝ) := by
  have h2 : (lam (Fin.last n) : ℝ) ≤ lam 0 := by exact_mod_cast h (Fin.zero_le _)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
  unfold Wnum; push_cast; linarith

theorem third_zeta_dimension_bound : WeylDimensionBounds := by
  intro n lam h
  have hW := one_le_weyl_numerator lam h
  have hlow : 1 ≤ weylDim lam := by
    unfold weylDim
    calc (1:ℝ) = ∏ i : Fin (n + 1), ∏ j ∈ univ.filter (fun j => i < j), (1:ℝ) := by simp
      _ ≤ _ := by
        refine Finset.prod_le_prod (fun i _ => by simp) fun i _ => ?_
        refine Finset.prod_le_prod (fun j _ => zero_le_one) fun j hj => ?_
        exact (weyl_factor_bounds lam h i j (Finset.mem_filter.1 hj).2).1
  refine ⟨hlow, ?_⟩
  have hup : weylDim lam ≤ (Wnum lam : ℝ) ^ ((n + 1) * (n + 1)) := by
    unfold weylDim
    calc _ ≤ ∏ _i : Fin (n + 1), (Wnum lam : ℝ) ^ (n + 1) := by
          refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j hj => ?_) fun i _ => ?_
          · exact le_trans zero_le_one (weyl_factor_bounds lam h i j (Finset.mem_filter.1 hj).2).1
          · calc _ ≤ ∏ j ∈ univ.filter (fun j => i < j), (Wnum lam : ℝ) := by
                  refine Finset.prod_le_prod (fun j hj => ?_) fun j hj => ?_
                  · exact le_trans zero_le_one (weyl_factor_bounds lam h i j (Finset.mem_filter.1 hj).2).1
                  · exact (weyl_factor_bounds lam h i j (Finset.mem_filter.1 hj).2).2
              _ = (Wnum lam : ℝ) ^ (univ.filter (fun j => i < j)).card := by simp
              _ ≤ (Wnum lam : ℝ) ^ (n + 1) := by
                  refine pow_le_pow_right₀ hW ?_
                  calc _ ≤ (univ : Finset (Fin (n + 1))).card := Finset.card_filter_le _ _
                    _ = n + 1 := by simp
      _ = _ := by simp [pow_mul]
  calc Real.log (weylDim lam) ≤ Real.log ((Wnum lam : ℝ) ^ ((n + 1) * (n + 1))) :=
        Real.log_le_log (by linarith) hup
    _ = _ := by rw [Real.log_pow]; push_cast; ring

private lemma shifted_product_telescoping (a M : ℕ) : ∀ c, c ≤ a →
    (∏ j ∈ range c, (a - j + M + 1)) * (a - c + M + 1) = (a + M + 1) * ∏ j ∈ range c, (a - j + M)
  | 0, _ => by simp
  | c + 1, h => by
    rw [prod_range_succ, prod_range_succ]
    have ih := shifted_product_telescoping a M c (by omega)
    have e : a - (c + 1) + M + 1 = a - c + M := by omega
    rw [e]
    calc _ = ((∏ j ∈ range c, (a - j + M + 1)) * (a - c + M + 1)) * (a - c + M) := by ring
      _ = _ := by rw [ih]; ring

private lemma hook_row_product_eq_factorial (a : ℕ) (μ : ℕ → ℕ) : ∀ M, (∀ k l, k ≤ l → l < M → μ l ≤ μ k) →
    (∀ k, k < M → μ k ≤ a) →
    (∏ j ∈ range a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0))
      * ∏ k ∈ range M, (a - μ k + k + 1) = (a + M).factorial
  | 0, _, _ => by
    simp only [range_zero, sum_empty, prod_empty, add_zero, mul_one]
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]
    refine prod_congr rfl fun j hj => ?_
    have := mem_range.1 hj
    omega
  | M + 1, hanti, hle => by
    have ih := hook_row_product_eq_factorial a μ M (fun k l hkl hl => hanti k l hkl (by omega)) (fun k hk => hle k (by omega))
    have hc : μ M ≤ a := hle M (by omega)
    have key : (∏ j ∈ range a, (a - j + ∑ k ∈ range (M + 1), if j < μ k then 1 else 0))
        * (a - μ M + M + 1)
        = (a + M + 1) * ∏ j ∈ range a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0) := by
      rw [← prod_range_mul_prod_Ico _ hc, ← prod_range_mul_prod_Ico _ hc]
      have h1 : ∏ j ∈ range (μ M), (a - j + ∑ k ∈ range (M + 1), if j < μ k then 1 else 0)
          = ∏ j ∈ range (μ M), (a - j + M + 1) := by
        refine prod_congr rfl fun j hj => ?_
        have hj' := mem_range.1 hj
        have : ∑ k ∈ range (M + 1), (if j < μ k then 1 else 0) = ∑ k ∈ range (M + 1), 1 := by
          refine sum_congr rfl fun k hk => ?_
          have hk' := mem_range.1 hk
          have := hanti k M (by omega) (by omega)
          rw [if_pos (by omega)]
        rw [this]; simp; ring
      have h2 : ∏ j ∈ range (μ M), (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0)
          = ∏ j ∈ range (μ M), (a - j + M) := by
        refine prod_congr rfl fun j hj => ?_
        have hj' := mem_range.1 hj
        have : ∑ k ∈ range M, (if j < μ k then 1 else 0) = ∑ k ∈ range M, 1 := by
          refine sum_congr rfl fun k hk => ?_
          have hk' := mem_range.1 hk
          have := hanti k M (by omega) (by omega)
          rw [if_pos (by omega)]
        rw [this]; simp
      have h3 : ∏ j ∈ Ico (μ M) a, (a - j + ∑ k ∈ range (M + 1), if j < μ k then 1 else 0)
          = ∏ j ∈ Ico (μ M) a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0) := by
        refine prod_congr rfl fun j hj => ?_
        have hj' := mem_Ico.1 hj
        rw [sum_range_succ, if_neg (by omega), add_zero]
      rw [h1, h2, h3]
      have ht := shifted_product_telescoping a M (μ M) hc
      calc _ = ((∏ j ∈ range (μ M), (a - j + M + 1)) * (a - μ M + M + 1))
              * ∏ j ∈ Ico (μ M) a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0) := by ring
        _ = _ := by rw [ht]; ring
    rw [prod_range_succ (fun k => a - μ k + k + 1)]
    calc _ = ((∏ j ∈ range a, (a - j + ∑ k ∈ range (M + 1), if j < μ k then 1 else 0))
              * (a - μ M + M + 1)) * ∏ k ∈ range M, (a - μ k + k + 1) := by ring
      _ = (a + M + 1) * ((∏ j ∈ range a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0))
              * ∏ k ∈ range M, (a - μ k + k + 1)) := by rw [key]; ring
      _ = _ := by rw [ih, ← add_assoc, Nat.factorial_succ]

private lemma prod_filter_gt_eq_prod_range {α : Type} [CommMonoid α] {N : ℕ} (i : Fin N) (g : ℕ → α) :
    ∏ j ∈ (univ : Finset (Fin N)).filter (fun j => i < j), g j
      = ∏ k ∈ range (N - (i + 1)), g (i + 1 + k) := by
  rw [prod_filter]
  have h1 : ∏ j : Fin N, (if i < j then g j else 1)
      = ∏ n ∈ range N, (if (i : ℕ) < n then g n else 1) :=
    Fin.prod_univ_eq_prod_range (fun n => if (i : ℕ) < n then g n else 1) N
  rw [h1, ← prod_range_mul_prod_Ico _ (show (i : ℕ) + 1 ≤ N from i.2), prod_Ico_eq_prod_range]
  rw [prod_eq_one, one_mul]
  · refine prod_congr rfl fun k _ => ?_
    rw [if_pos]; omega
  · intro n hn
    have := mem_range.1 hn
    rw [if_neg]; omega

private lemma sum_filter_gt_eq_sum_range {N : ℕ} (i : Fin N) (g : ℕ → ℕ) :
    ∑ j ∈ (univ : Finset (Fin N)).filter (fun j => i < j), g j
      = ∑ k ∈ range (N - (i + 1)), g (i + 1 + k) := by
  rw [sum_filter]
  have h1 : ∑ j : Fin N, (if i < j then g j else 0)
      = ∑ n ∈ range N, (if (i : ℕ) < n then g n else 0) :=
    Fin.sum_univ_eq_sum_range (fun n => if (i : ℕ) < n then g n else 0) N
  rw [h1, ← sum_range_add_sum_Ico _ (show (i : ℕ) + 1 ≤ N from i.2), sum_Ico_eq_sum_range]
  rw [sum_eq_zero, zero_add]
  · refine sum_congr rfl fun k _ => ?_
    rw [if_pos]; omega
  · intro n hn
    have := mem_range.1 hn
    rw [if_neg]; omega

private lemma hook_row_identity_fin {N : ℕ} (nu : Fin N → ℕ) (h : Antitone nu) (i : Fin N) :
    (∏ j ∈ range (nu i), hookLen nu i j)
      * ∏ j ∈ univ.filter (fun j => i < j), (nu i - nu j + ((j : ℕ) - (i : ℕ)))
      = (nu i + N - 1 - i).factorial := by
  set ν' : ℕ → ℕ := fun n => if hn : n < N then nu ⟨n, hn⟩ else 0 with hν'
  have hv : ∀ j : Fin N, ν' j = nu j := fun j => by simp [hν']
  have hanti : ∀ p q, p ≤ q → q < N → ν' q ≤ ν' p := by
    intro p q hpq hq
    have hp : p < N := by omega
    simp only [hν', dif_pos hp, dif_pos hq]
    exact h (by simpa using hpq)
  have e1 : ∏ j ∈ univ.filter (fun j => i < j), (nu i - nu j + ((j : ℕ) - (i : ℕ)))
      = ∏ k ∈ range (N - (i + 1)), (nu i - ν' (i + 1 + k) + k + 1) := by
    have := prod_filter_gt_eq_prod_range i (fun n => nu i - ν' n + (n - (i : ℕ)))
    simp only [hv] at this
    rw [this]
    refine prod_congr rfl fun k _ => ?_
    omega
  have e2 : ∀ j, hookLen nu i j
      = nu i - j + ∑ k ∈ range (N - (i + 1)), if j < ν' (i + 1 + k) then 1 else 0 := by
    intro j
    unfold hookLen
    rw [← filter_filter, card_filter]
    have := sum_filter_gt_eq_sum_range i (fun n => if j < ν' n then 1 else 0)
    simp only [hv] at this
    rw [this]
  rw [e1, prod_congr rfl (fun j _ => e2 j)]
  have := hook_row_product_eq_factorial (nu i) (fun k => ν' (i + 1 + k)) (N - (i + 1))
    (fun k l hkl hl => hanti _ _ (by omega) (by omega))
    (fun k hk => by
      have := hanti i (i + 1 + k) (by omega) (by omega)
      rwa [hv] at this)
  rw [this]
  congr 1
  have := i.2
  omega

theorem hook_length_formula : HookLengthFormula := by
  intro N nu h
  have hden : ∀ i : Fin N, ∏ j ∈ univ.filter (fun j => i < j), (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ)
      = ((∏ j ∈ univ.filter (fun j => i < j), (nu i - nu j + ((j : ℕ) - (i : ℕ))) : ℕ) : ℝ) := by
    intro i
    rw [Nat.cast_prod]
    refine prod_congr rfl fun j hj => ?_
    have hij : i < j := (mem_filter.1 hj).2
    have h1 : nu j ≤ nu i := h hij.le
    have h2 : (i : ℕ) ≤ j := hij.le
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  have hpos : ∀ i : Fin N,
      0 < ∏ j ∈ univ.filter (fun j => i < j), (nu i - nu j + ((j : ℕ) - (i : ℕ))) := by
    intro i
    refine prod_pos fun j hj => ?_
    have hij : (i : ℕ) < j := (mem_filter.1 hj).2
    omega
  unfold hookF
  rw [eq_div_iff]
  · rw [prod_congr rfl (fun i _ => hden i)]
    unfold hookProd
    rw [Nat.cast_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [← Nat.cast_mul, hook_row_identity_fin nu h i]
  · rw [prod_congr rfl (fun i _ => hden i)]
    refine prod_ne_zero_iff.2 fun i _ => ?_
    exact_mod_cast (hpos i).ne'

private lemma one_le_hook_product {N : ℕ} (nu : Fin N → ℕ) : 1 ≤ hookProd nu := by
  unfold hookProd
  refine Nat.succ_le_of_lt (prod_pos fun i _ => prod_pos fun j hj => ?_)
  have := mem_range.1 hj
  unfold hookLen
  omega

private lemma log_factorial_le_mul_log (n : ℕ) (M : ℝ) (hM : 1 ≤ M) (h : (n : ℝ) ≤ M) :
    Real.log (n.factorial : ℝ) ≤ M * Real.log M := by
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := by
          refine Real.log_le_log (by exact_mod_cast n.factorial_pos) ?_
          exact_mod_cast Nat.factorial_le_pow n
      _ = n * Real.log n := by rw [Real.log_pow]
      _ ≤ n * Real.log M := by
          exact mul_le_mul_of_nonneg_left (Real.log_le_log hn' h) hn'.le
      _ ≤ M * Real.log M := mul_le_mul_of_nonneg_right h hlM

theorem thin_partition_bound : ThinPlaceHookBound := by
  intro C₀ hC
  refine ⟨(3 + C₀) * (Real.log (3 + C₀) + 1) + (2 + C₀) * C₀, ?_⟩
  intro R nu b' L logOm hanti hrow hb hL hlb hR hOm
  have hl3 : 0 ≤ Real.log (3 + C₀) := Real.log_nonneg (by linarith)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  set M : ℝ := (3 + C₀) * b' with hMdef
  have hM1 : 1 ≤ M := by nlinarith
  have hlogM : Real.log M ≤ (Real.log (3 + C₀) + 1) * L := by
    rw [hMdef, Real.log_mul (by linarith) (by linarith)]
    nlinarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hform : (hookProd nu : ℝ) = hookF nu := hook_length_formula (R + 1) nu hanti
  have hF1 : 1 ≤ hookF nu := by
    rw [← hform]; exact_mod_cast one_le_hook_product nu
  have hlow : 0 ≤ Real.log (hookF nu) := Real.log_nonneg hF1
  have hup : Real.log (hookF nu) ≤ ((R : ℝ) + 1) * (M * Real.log M) := by
    have h1 := (Formalism.LogVandermondeBounds.flipTwoThree.hook_product_bounds R nu hanti).1
    calc Real.log (hookF nu)
        ≤ Real.log (∏ i : Fin (R + 1), ((nu i + R - i : ℕ).factorial : ℝ)) :=
          Real.log_le_log (by linarith) h1
      _ = ∑ i : Fin (R + 1), Real.log ((nu i + R - i : ℕ).factorial : ℝ) := by
          rw [Real.log_prod]
          intro i _
          exact_mod_cast (Nat.factorial_pos _).ne'
      _ ≤ ∑ _i : Fin (R + 1), M * Real.log M := by
          refine sum_le_sum fun i _ => log_factorial_le_mul_log _ M hM1 ?_
          have h2 : ((nu i + R - i : ℕ) : ℝ) ≤ (nu i : ℝ) + R := by
            exact_mod_cast Nat.sub_le _ _
          have h3 := hrow i
          rw [hMdef]; nlinarith
      _ = _ := by simp
  have hS0 : 0 ≤ ∑ i, (nu i : ℝ) := sum_nonneg fun i _ => Nat.cast_nonneg _
  have hS : ∑ i, (nu i : ℝ) ≤ ((R : ℝ) + 1) * ((2 + C₀) * b') := by
    calc ∑ i, (nu i : ℝ) ≤ ∑ _i : Fin (R + 1), (2 + C₀) * b' := sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  unfold placeTerm
  have hSO : |(∑ i, (nu i : ℝ)) * logOm| ≤ ((R : ℝ) + 1) * ((2 + C₀) * b') * (C₀ * L) := by
    rw [abs_mul, abs_of_nonneg hS0]
    exact mul_le_mul hS hOm (abs_nonneg _) (by positivity)
  have hML : M * Real.log M ≤ M * ((Real.log (3 + C₀) + 1) * L) :=
    mul_le_mul_of_nonneg_left hlogM (by linarith)
  have hup2 : ((R : ℝ) + 1) * (M * Real.log M) ≤ ((R : ℝ) + 1) * (M * ((Real.log (3 + C₀) + 1) * L)) :=
    mul_le_mul_of_nonneg_left hML (by linarith)
  calc |Real.log (hookF nu) - (∑ i, (nu i : ℝ)) * logOm|
      ≤ |Real.log (hookF nu)| + |(∑ i, (nu i : ℝ)) * logOm| := abs_sub _ _
    _ ≤ ((R : ℝ) + 1) * (M * ((Real.log (3 + C₀) + 1) * L))
          + ((R : ℝ) + 1) * ((2 + C₀) * b') * (C₀ * L) := by
        rw [abs_of_nonneg hlow]; linarith
    _ = _ := by rw [hMdef]; ring

end Formalism.HermitianLattices.TraceIntegrality
