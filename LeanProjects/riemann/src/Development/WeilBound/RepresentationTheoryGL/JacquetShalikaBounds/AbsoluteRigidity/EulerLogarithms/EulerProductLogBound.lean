import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

noncomputable section

open scoped ComplexConjugate

namespace PositivityTheory.RgJS

namespace EulerProductLogLemmas

variable {W : Type} {A B : Type} [Fintype A] [Fintype B]

def zz (q : W → ℕ) (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ) (w : W) (a : A) (b : B) : ℂ :=
  α w a * conj (β w b) * (q w : ℂ) ^ (-s)

theorem lterm_eq (q : W → ℕ) (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ) (p : W × ℕ) :
    lterm q α β s p = ∑ a, ∑ b, zz q α β s p.1 a b ^ (p.2 + 1) / ((p.2 : ℂ) + 1) := by
  rw [lterm, map_sum, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun (a : A) _ => ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun (b : B) _ => ?_
  rw [zz, map_pow]
  ring

omit [Fintype A] [Fintype B] in
theorem norm_zz_le {q : W → ℕ} {α : W → A → ℂ} {β : W → B → ℂ} {s : ℂ} (hq : ∀ w, 2 ≤ q w)
    (hα : ∀ w a, ‖α w a‖ ≤ Real.sqrt (q w)) (hβ : ∀ w b, ‖β w b‖ ≤ Real.sqrt (q w)) (w : W) (a : A) (b : B) :
    ‖zz q α β s w a b‖ ≤ (q w : ℝ) ^ (1 - s.re) := by
  have hq0 : (0 : ℝ) < q w := by have := hq w; positivity
  have hqn : 0 < q w := by have := hq w; omega
  rw [zz, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_natCast_cpow_of_pos hqn, Complex.neg_re,
    sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_one]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hq0.le _)
  calc ‖α w a‖ * ‖β w b‖ ≤ Real.sqrt (q w) * Real.sqrt (q w) :=
        mul_le_mul (hα w a) (hβ w b) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = q w := Real.mul_self_sqrt hq0.le

theorem x_le_half {q : W → ℕ} {s : ℂ} (hq : ∀ w, 2 ≤ q w) (hs : 2 < s.re) (w : W) :
    (q w : ℝ) ^ (1 - s.re) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ q w := by exact_mod_cast hq w
  have h1 : (1 : ℝ) ≤ q w := by linarith
  calc (q w : ℝ) ^ (1 - s.re) ≤ (q w : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = (q w : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

theorem x_nonneg {q : W → ℕ} (s : ℂ) (w : W) : 0 ≤ (q w : ℝ) ^ (1 - s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _

def maj (q : W → ℕ) (s : ℂ) (C : ℝ) (p : W × ℕ) : ℝ := C * ((q p.1 : ℝ) ^ (1 - s.re)) ^ (p.2 + 1)

theorem summable_maj {q : W → ℕ} {s : ℂ} (hP : Primes q) (hs : 2 < s.re) {C : ℝ} (hC : 0 ≤ C) :
    Summable (maj q s C) := by
  have hx := x_le_half hP.two hs
  have hxn := x_nonneg (q := q) s
  have hgeo : ∀ w, HasSum (fun k : ℕ => C * ((q w : ℝ) ^ (1 - s.re)) ^ (k + 1))
      (C * ((q w : ℝ) ^ (1 - s.re) * (1 - (q w : ℝ) ^ (1 - s.re))⁻¹)) := by
    intro w
    have h := hasSum_geometric_of_lt_one (hxn w) (by linarith [hx w])
    have h2 := (h.mul_left ((q w : ℝ) ^ (1 - s.re))).mul_left C
    have e : (fun k : ℕ => C * ((q w : ℝ) ^ (1 - s.re)) ^ (k + 1)) =
        fun i => C * ((q w : ℝ) ^ (1 - s.re) * ((q w : ℝ) ^ (1 - s.re)) ^ i) := funext fun k => by rw [pow_succ']
    rw [e]; exact h2
  refine (summable_prod_of_nonneg (fun p => mul_nonneg hC (pow_nonneg (hxn p.1) _))).2
    ⟨fun w => (hgeo w).summable, ?_⟩
  have hconv := hP.conv (s.re - 1) (by linarith)
  refine Summable.of_nonneg_of_le (fun w => ?_) (fun w => ?_) (hconv.mul_left (2 * C))
  · rw [(hgeo w).tsum_eq]
    have : 0 < 1 - (q w : ℝ) ^ (1 - s.re) := by linarith [hx w]
    exact mul_nonneg hC (mul_nonneg (hxn w) (inv_nonneg.2 this.le))
  · rw [(hgeo w).tsum_eq]
    have e : (q w : ℝ) ^ (-(s.re - 1)) = (q w : ℝ) ^ (1 - s.re) := by congr 1; ring
    rw [e]
    have h1 : (1 - (q w : ℝ) ^ (1 - s.re))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith [hx w]) (by norm_num)]
      linarith [hx w]
    calc C * ((q w : ℝ) ^ (1 - s.re) * (1 - (q w : ℝ) ^ (1 - s.re))⁻¹)
        ≤ C * ((q w : ℝ) ^ (1 - s.re) * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (hxn w)) hC
      _ = 2 * C * (q w : ℝ) ^ (1 - s.re) := by ring

theorem norm_lterm_le {q : W → ℕ} {α : W → A → ℂ} {β : W → B → ℂ} {s : ℂ} (hq : ∀ w, 2 ≤ q w)
    (hα : ∀ w a, ‖α w a‖ ≤ Real.sqrt (q w)) (hβ : ∀ w b, ‖β w b‖ ≤ Real.sqrt (q w)) (p : W × ℕ) :
    ‖lterm q α β s p‖ ≤ maj q s (Fintype.card A * Fintype.card B) p := by
  rw [lterm_eq, maj]
  have hd : (1 : ℝ) ≤ ‖((p.2 : ℂ) + 1)‖ := by
    have : ((p.2 : ℂ) + 1) = ((p.2 + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos _
  have hterm : ∀ a b, ‖zz q α β s p.1 a b ^ (p.2 + 1) / ((p.2 : ℂ) + 1)‖ ≤ ((q p.1 : ℝ) ^ (1 - s.re)) ^ (p.2 + 1) := by
    intro a b
    rw [norm_div, norm_pow]
    refine (div_le_self (pow_nonneg (norm_nonneg _) _) hd).trans ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_zz_le hq hα hβ p.1 a b) _
  calc ‖∑ a, ∑ b, zz q α β s p.1 a b ^ (p.2 + 1) / ((p.2 : ℂ) + 1)‖
      ≤ ∑ a : A, ∑ b : B, ((q p.1 : ℝ) ^ (1 - s.re)) ^ (p.2 + 1) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b _ => hterm a b))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end EulerProductLogLemmas

open EulerProductLogLemmas in
theorem euler_product_log_bound : EulerLog := by
  intro W q A B _ _ α β s hP hα hβ hs
  have hq := hP.two
  have hsumn : Summable (fun p => ‖lterm q α β s p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (norm_lterm_le hq hα hβ)
      (summable_maj hP hs (by positivity))
  have hlt : ∀ w a b, ‖zz q α β s w a b‖ < 1 := fun w a b =>
    (norm_zz_le hq hα hβ w a b).trans_lt (by linarith [x_le_half hq hs w])
  have hfib : ∀ w, HasSum (fun k => lterm q α β s (w, k)) (∑ a, ∑ b, -Complex.log (1 - zz q α β s w a b)) := by
    intro w
    simp only [lterm_eq]
    exact hasSum_sum fun a _ => hasSum_sum fun b _ => Complex.hasSum_taylorSeries_neg_log' (hlt w a b)
  have hall : HasSum (lterm q α β s) (∑' p, lterm q α β s p) := (hsumn.of_norm).hasSum
  have hw : HasSum (fun w => ∑ a, ∑ b, -Complex.log (1 - zz q α β s w a b)) (∑' p, lterm q α β s p) :=
    hall.prod_fiberwise hfib
  have hprod := hw.cexp
  have e : ∀ w, (Complex.exp ∘ fun w => ∑ a, ∑ b, -Complex.log (1 - zz q α β s w a b)) w =
      ∏ a, ∏ b, (1 - α w a * conj (β w b) * (q w : ℂ) ^ (-s))⁻¹ := by
    intro w
    simp only [Function.comp_apply, Complex.exp_sum]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    have h0 : (1 - zz q α β s w a b) ≠ 0 := by
      intro h
      have := hlt w a b
      rw [show zz q α β s w a b = 1 by linear_combination -h, norm_one] at this
      exact lt_irrefl _ this
    rw [Complex.exp_neg, Complex.exp_log h0]
    rfl
  simp only [funext e] at hprod
  exact ⟨hsumn, hprod.tprod_eq, hprod.multipliable⟩

end PositivityTheory.RgJS
