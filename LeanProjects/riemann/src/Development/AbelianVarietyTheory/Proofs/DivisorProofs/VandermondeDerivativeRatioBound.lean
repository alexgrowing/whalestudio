import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho

open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.FlagHook

theorem iterate_pderiv_C_mul {σ : Type} (i : σ) (n : ℕ) (c : ℝ) (P : MvPolynomial σ ℝ) :
    (pderiv i)^[n] (C c * P) = C c * (pderiv i)^[n] P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, pderiv_C_mul]

theorem iterate_pderiv_sum {σ κ : Type} (i : σ) (n : ℕ) (S : Finset κ) (P : κ → MvPolynomial σ ℝ) :
    (pderiv i)^[n] (∑ k ∈ S, P k) = ∑ k ∈ S, (pderiv i)^[n] (P k) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sum]

theorem pderiv_prod_of_const {σ κ : Type} [DecidableEq κ] (i : σ) (S : Finset κ)
    (f : κ → MvPolynomial σ ℝ) (e : κ → ℝ) (he : ∀ k, pderiv i (f k) = C (e k)) :
    pderiv i (∏ k ∈ S, f k) = ∑ k ∈ S, C (e k) * ∏ l ∈ S.erase k, f l := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [prod_insert ha, sum_insert ha, erase_insert ha, pderiv_mul, he, ih, mul_sum]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    have hak : a ≠ k := fun h => ha (h ▸ hk)
    rw [erase_insert_of_ne hak, prod_insert (fun h => ha (mem_of_mem_erase h))]
    ring

theorem abs_eval_iterate_pderiv_prod_le {σ κ : Type} [DecidableEq κ] (i : σ) (v : σ → ℝ)
    (f : κ → MvPolynomial σ ℝ) (e w : κ → ℝ) (T : ℝ) (he : ∀ k, pderiv i (f k) = C (e k))
    (n : ℕ) (S : Finset κ) (hw : ∀ k ∈ S, 0 ≤ w k) (hew : ∀ k ∈ S, |e k| ≤ w k * |eval v (f k)|)
    (hT : ∑ k ∈ S, w k ≤ T) :
    |eval v ((pderiv i)^[n] (∏ k ∈ S, f k))| ≤ T ^ n * |eval v (∏ k ∈ S, f k)| := by
  induction n generalizing S with
  | zero => simp
  | succ n ih =>
    have hT0 : 0 ≤ T := (sum_nonneg hw).trans hT
    rw [Function.iterate_succ_apply, pderiv_prod_of_const i S f e he, iterate_pderiv_sum, map_sum]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ S, |eval v ((pderiv i)^[n] (C (e k) * ∏ l ∈ S.erase k, f l))|
        ≤ ∑ k ∈ S, w k * (T ^ n * |eval v (∏ k ∈ S, f k)|) := by
          refine sum_le_sum fun k hk => ?_
          have h1 := ih (S.erase k) (fun l hl => hw l (mem_of_mem_erase hl))
            (fun l hl => hew l (mem_of_mem_erase hl))
            ((sum_le_sum_of_subset_of_nonneg (erase_subset k S) fun l hl _ => hw l hl).trans hT)
          rw [iterate_pderiv_C_mul, map_mul, eval_C, abs_mul, ← mul_prod_erase S f hk, map_mul,
            abs_mul]
          calc |e k| * |eval v ((pderiv i)^[n] (∏ l ∈ S.erase k, f l))|
              ≤ (w k * |eval v (f k)|) * (T ^ n * |eval v (∏ l ∈ S.erase k, f l)|) :=
                mul_le_mul (hew k hk) h1 (abs_nonneg _) (mul_nonneg (hw k hk) (abs_nonneg _))
            _ = _ := by ring
      _ = (∑ k ∈ S, w k) * (T ^ n * |eval v (∏ k ∈ S, f k)|) := by rw [sum_mul]
      _ ≤ T * (T ^ n * |eval v (∏ k ∈ S, f k)|) :=
          mul_le_mul_of_nonneg_right hT (by positivity)
      _ = _ := by ring

theorem detE_rho_eq_C_mul_prod (N : ℕ) :
    ∃ c : ℝ, detE (rho N) =
      C c * ∏ p ∈ (univ : Finset (Fin N)).sigma (fun a => Ioi a), (X p.2 - X p.1) := by
  have h : (Matrix.of fun i c : Fin N =>
      (C ((((rho N) c).factorial : ℝ)⁻¹) * X i ^ (rho N) c : MvPolynomial (Fin N) ℝ)) =
      Matrix.of fun i c : Fin N => C ((((rho N) c).factorial : ℝ)⁻¹) *
        ((Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) ℝ)).submatrix id Fin.revPerm) i c := by
    ext i c : 2
    have : (rho N) c = ((Fin.rev c : Fin N) : ℕ) := by simp [rho, Fin.val_rev]; omega
    simp [Matrix.vandermonde_apply, this]
  refine ⟨(∏ c : Fin N, (((rho N) c).factorial : ℝ)⁻¹) *
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤ) : ℝ), ?_⟩
  rw [detE, h, Matrix.det_mul_row, Matrix.det_permute', Matrix.det_vandermonde, prod_sigma,
    map_mul, map_prod, map_intCast, mul_assoc]

theorem abs_iterate_pderiv_detE_rho_div_le (N n : ℕ) (v : Fin N → ℝ) (i : Fin N) (g : ℝ)
    (hg : 0 < g) (_hv : ∀ a b, a ≠ b → v a ≠ v b) (hs : ∀ a, a ≠ i → g ≤ |v i - v a|) :
    |eval v ((pderiv i)^[n] (detE (rho N))) / eval v (detE (rho N))| ≤ ((N : ℝ) / g) ^ n := by
  obtain ⟨c, hc⟩ := detE_rho_eq_C_mul_prod N
  have key := abs_eval_iterate_pderiv_prod_le (κ := (_ : Fin N) × Fin N) i v
    (fun p => X p.2 - X p.1)
    (fun p => (if p.2 = i then 1 else 0) - (if p.1 = i then 1 else 0))
    (fun p => ((if p.2 = i then 1 else 0) + (if p.1 = i then 1 else 0)) / g) ((N : ℝ) / g)
    (by
      rintro ⟨a, b⟩
      simp only [map_sub, pderiv_X, Pi.single_apply]
      split_ifs <;> simp)
    n ((univ : Finset (Fin N)).sigma (fun a => Ioi a))
    (by intro p _; split_ifs <;> positivity)
    (by
      rintro ⟨a, b⟩ hp
      have hab : a < b := by simpa using hp
      simp only [map_sub, eval_X]
      by_cases hb : b = i
      · have ha : a ≠ i := hb ▸ hab.ne
        have := hs a ha
        simp only [hb, ha, if_true, if_false, sub_zero, add_zero, abs_one]
        rw [div_mul_eq_mul_div, one_mul, one_le_div hg]
        exact this
      · by_cases ha : a = i
        · have := hs b hb
          simp only [hb, ha, if_true, if_false, zero_sub, zero_add, abs_neg, abs_one]
          rw [div_mul_eq_mul_div, one_mul, one_le_div hg, abs_sub_comm]
          exact this
        · simp [ha, hb])
    (by
      rw [← sum_div]
      refine div_le_div_of_nonneg_right ?_ hg.le
      rw [sum_sigma]
      simp only [sum_add_distrib]
      have h1 : ∑ a : Fin N, ∑ b ∈ Ioi a, (if b = i then (1 : ℝ) else 0) = (i : ℕ) := by
        simp only [sum_ite_eq', mem_Ioi]
        rw [sum_boole]
        have : (univ.filter fun a : Fin N => a < i) = Iio i := by ext; simp
        rw [this, Fin.card_Iio]
      have h2 : ∑ a : Fin N, ∑ _b ∈ Ioi a, (if a = i then (1 : ℝ) else 0) = ((N - 1 - i : ℕ) : ℝ) := by
        rw [sum_eq_single i (by intro a _ ha; simp [ha]) (by simp)]
        simp
      rw [h1, h2]
      have := i.2
      exact_mod_cast (by omega : (i : ℕ) + (N - 1 - i) ≤ N))
  rw [abs_div]
  refine div_le_of_le_mul₀ (abs_nonneg _) (by positivity) ?_
  rw [hc, iterate_pderiv_C_mul, map_mul, map_mul, abs_mul, abs_mul]
  calc _ ≤ |eval v (C c)| * (((N : ℝ) / g) ^ n * _) :=
        mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = _ := by ring

end GlobalTheory.FlagHook
