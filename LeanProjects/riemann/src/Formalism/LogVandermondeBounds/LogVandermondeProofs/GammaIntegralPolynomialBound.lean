import Formalism.LogVandermondeBounds.MultinomialPowerBound
import Mathlib

namespace Formalism.LogVandermondeBounds.flipTwoThree

open Finset MeasureTheory

theorem jet_exponential_bound : MinRatioPowerExponentialBound := by
  intro n g hg
  simp only
  have hg0 : (0:ℝ) < g := by exact_mod_cast hg
  have hE : (4:ℝ) ≤ 2 * Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  by_cases hng : n ≤ g
  · have he : (if n = 0 then (1:ℝ) else min 1 ((g:ℝ)/n)) = 1 := by
      split_ifs with h
      · rfl
      · have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h
        apply min_eq_left
        rw [le_div_iff₀ hn, one_mul]
        exact_mod_cast hng
    rw [he]
    simp only [one_pow, inv_one, one_mul]
    calc (1+1:ℝ)^(n+g) ≤ (1+1)^(g+g) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 4^g := by rw [show g + g = 2 * g by ring, pow_mul]; norm_num
      _ ≤ (2 * Real.exp 1)^g := pow_le_pow_left₀ (by norm_num) hE g
      _ ≤ _ := pow_le_pow_left₀ (by positivity)
          (le_mul_of_one_le_right (by positivity) (le_max_left _ _)) g
  · push Not at hng
    have hn0 : n ≠ 0 := by omega
    have hn : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hgn : (g:ℝ)/n < 1 := by
      rw [div_lt_one hn]; exact_mod_cast hng
    have he : (if n = 0 then (1:ℝ) else min 1 ((g:ℝ)/n)) = (g:ℝ)/n := by
      rw [if_neg hn0]; exact min_eq_right hgn.le
    rw [he]
    have hmax : max 1 ((n:ℝ)/g) = (n:ℝ)/g := by
      apply max_eq_right
      rw [le_div_iff₀ hg0, one_mul]; exact_mod_cast hng.le
    rw [hmax]
    have hx0 : 0 < (g:ℝ)/n := by positivity
    have h1 : (1+(g:ℝ)/n)^n ≤ Real.exp 1 ^ g := by
      calc (1+(g:ℝ)/n)^n ≤ (Real.exp ((g:ℝ)/n))^n :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((g:ℝ)/n)]) n
        _ = Real.exp (n * ((g:ℝ)/n)) := (Real.exp_nat_mul _ n).symm
        _ = Real.exp (g * 1) := by congr 1; field_simp
        _ = Real.exp 1 ^ g := Real.exp_nat_mul 1 g
    have h2 : (1+(g:ℝ)/n)^g ≤ 2^g := pow_le_pow_left₀ (by positivity) (by linarith) g
    have h3 : (((g:ℝ)/n)^g)⁻¹ = ((n:ℝ)/g)^g := by rw [← inv_pow, inv_div]
    rw [pow_add, h3, mul_pow, mul_pow]
    calc ((n:ℝ)/g)^g * ((1+(g:ℝ)/n)^n * (1+(g:ℝ)/n)^g)
        ≤ ((n:ℝ)/g)^g * (Real.exp 1 ^ g * 2^g) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2^g * Real.exp 1 ^ g * ((n:ℝ)/g)^g := by ring

lemma gamma_term (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-Real.pi * u)) (Set.Ioi 0) ∧
    ∫ u in Set.Ioi (0:ℝ), u ^ k * Real.exp (-Real.pi * u) = (k.factorial : ℝ) / Real.pi ^ (k+1) := by
  have hval : ∫ u in Set.Ioi (0:ℝ), u ^ k * Real.exp (-Real.pi * u)
      = (k.factorial : ℝ) / Real.pi ^ (k+1) := by
    have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k:ℝ) + 1) (r := Real.pi)
      (by positivity) Real.pi_pos
    have hc : ∫ u in Set.Ioi (0:ℝ), u ^ k * Real.exp (-Real.pi * u)
        = ∫ t in Set.Ioi (0:ℝ), t ^ ((k:ℝ) + 1 - 1) * Real.exp (-(Real.pi * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      simp only [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
    rw [hc, key, Real.Gamma_nat_eq_factorial]
    rw [show ((k:ℝ) + 1) = ((k+1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [one_div, inv_pow]
    ring
  refine ⟨?_, hval⟩
  apply Integrable.of_integral_ne_zero
  rw [hval]
  have := Real.pi_pos
  positivity

theorem gamma_integral_polynomial_bound : GammaIntegralBound := by
  intro v g hv
  have hfun : (fun u : ℝ => Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g)
      = fun u => ∑ k ∈ range (g+1),
          (Real.pi * (g.choose k : ℝ) * (4 * v) ^ k) * (u ^ k * Real.exp (-Real.pi * u)) := by
    funext u
    rw [add_comm, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [one_pow, mul_one, mul_pow, mul_pow]
    ring
  have hint : ∀ k ∈ range (g+1), Integrable
      (fun u : ℝ => (Real.pi * (g.choose k : ℝ) * (4 * v) ^ k) * (u ^ k * Real.exp (-Real.pi * u)))
      (volume.restrict (Set.Ioi 0)) :=
    fun k _ => (gamma_term k).1.const_mul _
  rw [hfun]
  refine ⟨by unfold IntegrableOn; exact integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  have hpi := Real.pi_pos
  rw [add_comm (1:ℝ) (4 * (g:ℝ) * v / Real.pi), add_pow]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hkg : k ≤ g := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [integral_const_mul, (gamma_term k).2, one_pow, mul_one]
  have hf : (k.factorial : ℝ) ≤ (g : ℝ) ^ k := by
    exact_mod_cast (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hkg k)
  have e1 : Real.pi * (g.choose k : ℝ) * (4 * v) ^ k * ((k.factorial : ℝ) / Real.pi ^ (k+1))
      = (g.choose k : ℝ) * (4 * v / Real.pi) ^ k * (k.factorial : ℝ) := by
    have hpk : Real.pi ^ k ≠ 0 := by positivity
    rw [div_pow, pow_succ]
    field_simp
    try ring
  have e2 : (4 * (g:ℝ) * v / Real.pi) ^ k * (g.choose k : ℝ)
      = (g.choose k : ℝ) * (4 * v / Real.pi) ^ k * (g:ℝ) ^ k := by
    rw [show 4 * (g:ℝ) * v / Real.pi = (4 * v / Real.pi) * g by ring, mul_pow]
    ring
  rw [e1, e2]
  gcongr

theorem amgm_period_lattice_bound : AmgmSumLowerBoundOfProd := by
  intro f v x hf hv hx hprod
  have hf0 : (0:ℝ) < f := by exact_mod_cast hf
  have hfne : f ≠ 0 := by omega
  have hw : ∑ _i : Fin f, (f:ℝ)⁻¹ = 1 := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have amgm := Real.geom_mean_le_arith_mean_weighted (s := univ) (fun _ => (f:ℝ)⁻¹) x
    (fun _ _ => by positivity) hw (fun i _ => (hx i).le)
  rw [Real.finsetProd_rpow _ _ (fun i _ => (hx i).le)] at amgm
  have hlow : (2 * v)⁻¹ ≤ (∏ i, x i) ^ ((f:ℝ)⁻¹) := by
    have h0 : (0:ℝ) ≤ ((2 * v) ^ f)⁻¹ := by positivity
    have := Real.rpow_le_rpow h0 hprod (by positivity : (0:ℝ) ≤ (f:ℝ)⁻¹)
    rw [← inv_pow, Real.pow_rpow_inv_natCast (by positivity) hfne] at this
    exact this
  have h := hlow.trans amgm
  rw [← Finset.mul_sum] at h
  have e : (f:ℝ) / v = 2 * f * (2 * v)⁻¹ := by field_simp
  rw [e]
  calc 2 * (f:ℝ) * (2 * v)⁻¹ ≤ 2 * f * ((f:ℝ)⁻¹ * ∑ i, x i) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * ∑ i, x i := by field_simp

lemma hook_den_bounds (N : ℕ) (nu : Fin (N+1) → ℕ) (hnu : Antitone nu) (i j : Fin (N+1))
    (hij : i < j) :
    (1:ℝ) ≤ (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ) ∧
      (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ) ≤ (nu 0 : ℝ) + N + 1 := by
  have h1 : nu j ≤ nu i := hnu hij.le
  have h2 : nu i ≤ nu 0 := hnu (Fin.zero_le i)
  have h3 : (i:ℕ) < j := hij
  have h4 : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  constructor
  · have : (1:ℤ) ≤ (nu i : ℤ) - nu j + j - i := by omega
    exact_mod_cast this
  · have : ((nu i : ℤ) - nu j + j - i) ≤ (nu 0 : ℤ) + N + 1 := by omega
    exact_mod_cast this

lemma fact_bound (a b N i : ℕ) (hab : a ≤ b) (hi : i ≤ N) :
    (a + N - i).factorial ≤ a.factorial * (b + N + 1) ^ (N + 1) := by
  have e := Nat.factorial_mul_descFactorial (n := a + N - i) (k := N - i) (by omega)
  have e2 : a + N - i - (N - i) = a := by omega
  rw [e2] at e
  rw [← e]
  apply Nat.mul_le_mul_left
  calc (a + N - i).descFactorial (N - i) ≤ (a + N - i) ^ (N - i) := Nat.descFactorial_le_pow _ _
    _ ≤ (b + N + 1) ^ (N - i) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (b + N + 1) ^ (N + 1) := Nat.pow_le_pow_right (by omega) (by omega)

theorem hook_product_bounds : HookProductBounds := by
  intro N nu hnu
  set D : ℝ := ∏ i : Fin (N+1), ∏ j ∈ univ.filter (fun j => i < j),
    (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ) with hD
  set num : ℝ := ∏ i : Fin (N + 1), ((nu i + N - i : ℕ).factorial : ℝ) with hnum
  set Mr : ℝ := (nu 0 : ℝ) + N + 1 with hMr
  have hM1 : (1:ℝ) ≤ Mr := by
    have h0 : (0:ℝ) ≤ (nu 0 : ℝ) + N := by positivity
    linarith [hMr]
  have hH : hookF nu = num / D := by
    unfold hookF
    congr 1
  have hD1 : 1 ≤ D := by
    rw [hD]
    calc (1:ℝ) = ∏ _i : Fin (N+1), ∏ _j ∈ univ.filter (fun j => _i < j), (1:ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro i _
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro j hj
        exact (hook_den_bounds N nu hnu i j (mem_filter.mp hj).2).1
  have hDM : D ≤ Mr ^ ((N + 1) ^ 2) := by
    rw [hD]
    calc _ ≤ ∏ _i : Fin (N+1), Mr ^ (N + 1) := by
          apply Finset.prod_le_prod
          · intro i _
            apply Finset.prod_nonneg
            intro j hj
            exact zero_le_one.trans (hook_den_bounds N nu hnu i j (mem_filter.mp hj).2).1
          · intro i _
            calc _ ≤ ∏ _j ∈ univ.filter (fun j => i < j), Mr := by
                  apply Finset.prod_le_prod
                  · intro j hj
                    exact zero_le_one.trans (hook_den_bounds N nu hnu i j (mem_filter.mp hj).2).1
                  · intro j hj
                    exact (hook_den_bounds N nu hnu i j (mem_filter.mp hj).2).2
              _ = Mr ^ (univ.filter (fun j => i < j)).card := prod_const _
              _ ≤ Mr ^ (N + 1) := by
                  apply pow_le_pow_right₀ hM1
                  calc _ ≤ (univ : Finset (Fin (N+1))).card := card_filter_le _ _
                    _ = N + 1 := by simp
      _ = Mr ^ ((N + 1) ^ 2) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, sq]
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hnum0 : 0 < num := by rw [hnum]; positivity
  have hnumM : num ≤ (∏ i : Fin (N + 1), ((nu i).factorial : ℝ)) * Mr ^ ((N + 1) ^ 2) := by
    rw [hnum]
    calc _ ≤ ∏ i : Fin (N + 1), (((nu i).factorial : ℝ) * Mr ^ (N + 1)) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro i _
          have := fact_bound (nu i) (nu 0) N i (hnu (Fin.zero_le i)) (Nat.lt_succ_iff.mp i.isLt)
          rw [hMr]
          exact_mod_cast this
      _ = _ := by rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← pow_mul, sq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hH]
    exact div_le_self hnum0.le hD1
  · rw [hH, Real.log_div hnum0.ne' hD0.ne', hnum,
      Real.log_prod (fun i _ => by positivity)]
    have hl : Real.log D ≤ ((N:ℝ) + 1) ^ 2 * Real.log Mr := by
      calc Real.log D ≤ Real.log (Mr ^ ((N + 1) ^ 2)) := Real.log_le_log hD0 hDM
        _ = ((N:ℝ) + 1) ^ 2 * Real.log Mr := by rw [Real.log_pow]; push_cast; ring
    linarith
  · rw [hH]
    have hp : 0 < ∏ i : Fin (N + 1), ((nu i).factorial : ℝ) := by positivity
    rw [div_div, div_le_iff₀ (mul_pos hD0 hp)]
    calc num ≤ (∏ i : Fin (N + 1), ((nu i).factorial : ℝ)) * Mr ^ ((N + 1) ^ 2) := hnumM
      _ ≤ Mr ^ ((N + 1) ^ 2) * (D * ∏ i : Fin (N + 1), ((nu i).factorial : ℝ)) := by
        nlinarith [pow_pos (lt_of_lt_of_le zero_lt_one hM1) ((N+1)^2)]

theorem multinomial_le_pow_card : MultinomialPowerBound := by
  intro k α
  have h1 : Nat.multinomial univ α ≤ k ^ (∑ i, α i) := by
    have key := Finset.sum_pow_eq_sum_piAntidiag (univ : Finset (Fin k)) (fun _ => (1:ℕ))
      (∑ i, α i)
    simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at key
    rw [key]
    exact Finset.single_le_sum (f := fun β => Nat.multinomial univ β)
      (fun _ _ => Nat.zero_le _) (by simp [mem_piAntidiag])
  have hspec := Nat.multinomial_spec univ α
  have hpos : (0:ℝ) < ∏ i, ((α i).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hpos]
  calc ((∑ i, α i).factorial : ℝ) = (∏ i, ((α i).factorial : ℝ)) * Nat.multinomial univ α := by
        exact_mod_cast hspec.symm
    _ ≤ (∏ i, ((α i).factorial : ℝ)) * (k : ℝ) ^ (∑ i, α i) := by
        gcongr
        exact_mod_cast h1
    _ = _ := by ring

end Formalism.LogVandermondeBounds.flipTwoThree
