import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LiftGrowth

open UpperHalfPlane hiding I
open GlobalTheory.HilbertThetaSeries.SlashCocycle

theorem abs_det_le (x : Matrix (Fin 2) (Fin 2) ℝ) (H : ℝ) (hx : ∀ i j, |x i j| ≤ H) : |x.det| ≤ 2 * H ^ 2 := by
  rw [Matrix.det_fin_two]
  have h0 : 0 ≤ H := (abs_nonneg _).trans (hx 0 0)
  have h1 : |x 0 0 * x 1 1| ≤ H * H := by rw [abs_mul]; exact mul_le_mul (hx _ _) (hx _ _) (abs_nonneg _) h0
  have h2 : |x 0 1 * x 1 0| ≤ H * H := by rw [abs_mul]; exact mul_le_mul (hx _ _) (hx _ _) (abs_nonneg _) h0
  have := abs_sub (x 0 0 * x 1 1) (x 0 1 * x 1 0)
  nlinarith

theorem place_bound (x : GL (Fin 2) ℝ) (hp : 0 < (x.det : ℝ)) (H : ℝ) (hx : ∀ i j, |x i j| ≤ H)
    (hy : ∀ i j, |(x⁻¹ : GL (Fin 2) ℝ) i j| ≤ H) :
    |(x.det : ℝ)| ≤ (2 * H) ^ 2 ∧ ‖denom x UpperHalfPlane.I‖⁻¹ ≤ 2 * H ∧
      (1 + ‖((x • UpperHalfPlane.I : ℍ) : ℂ)‖ ^ 2) / (x • UpperHalfPlane.I : ℍ).im ≤ (2 * H) ^ 4 := by
  have h0 : 0 ≤ H := (abs_nonneg _).trans (hx 0 0)
  have hd : 0 < ‖denom x UpperHalfPlane.I‖ := norm_pos_iff.2 (denom_ne_zero x _)
  have hdn : ‖denom x UpperHalfPlane.I‖ ^ 2 = x 1 0 ^ 2 + x 1 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [denom]; ring
  have hnn : ‖num x UpperHalfPlane.I‖ ^ 2 = x 0 0 ^ 2 + x 0 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [num]; ring
  have hsq : ∀ i j, x i j ^ 2 ≤ H ^ 2 := fun i j => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i j) 2
  refine ⟨?_, ?_, ?_⟩
  · have := abs_det_le x.val H hx
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    nlinarith
  · have e : x 1 0 * (x⁻¹ : GL (Fin 2) ℝ) 0 1 + x 1 1 * (x⁻¹ : GL (Fin 2) ℝ) 1 1 = 1 := by
      have := congrFun (congrFun x.val_inv 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have a1 : |x 1 0| ≤ ‖denom x UpperHalfPlane.I‖ := by
      apply abs_le_of_sq_le_sq _ hd.le |>.trans_eq' rfl
      nlinarith [sq_nonneg (x 1 1)]
    have a2 : |x 1 1| ≤ ‖denom x UpperHalfPlane.I‖ := by
      apply abs_le_of_sq_le_sq _ hd.le |>.trans_eq' rfl
      nlinarith [sq_nonneg (x 1 0)]
    have b1 : |x 1 0 * (x⁻¹ : GL (Fin 2) ℝ) 0 1| ≤ ‖denom x UpperHalfPlane.I‖ * H := by
      rw [abs_mul]; exact mul_le_mul a1 (hy _ _) (abs_nonneg _) hd.le
    have b2 : |x 1 1 * (x⁻¹ : GL (Fin 2) ℝ) 1 1| ≤ ‖denom x UpperHalfPlane.I‖ * H := by
      rw [abs_mul]; exact mul_le_mul a2 (hy _ _) (abs_nonneg _) hd.le
    rw [inv_eq_one_div, div_le_iff₀ hd]
    have c1 := le_abs_self (x 1 0 * (x⁻¹ : GL (Fin 2) ℝ) 0 1)
    have c2 := le_abs_self (x 1 1 * (x⁻¹ : GL (Fin 2) ℝ) 1 1)
    linarith
  · have hi : ((x.det : ℝ))⁻¹ ≤ 2 * H ^ 2 := by
      have := abs_det_le (x⁻¹ : GL (Fin 2) ℝ).val H hy
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val] at this
      exact (le_abs_self _).trans this
    have e : (1 + ‖((x • UpperHalfPlane.I : ℍ) : ℂ)‖ ^ 2) / (x • UpperHalfPlane.I : ℍ).im =
        (‖denom x UpperHalfPlane.I‖ ^ 2 + ‖num x UpperHalfPlane.I‖ ^ 2) * ((x.det : ℝ))⁻¹ := by
      rw [im_smul_eq_div_normSq, coe_smul_of_det_pos hp, abs_of_pos hp, norm_div, ← Complex.sq_norm]
      simp only [I_im]
      field_simp
    rw [e, hdn, hnn]
    have s : x 1 0 ^ 2 + x 1 1 ^ 2 + (x 0 0 ^ 2 + x 0 1 ^ 2) ≤ 4 * H ^ 2 := by
      linarith [hsq 0 0, hsq 0 1, hsq 1 0, hsq 1 1]
    calc _ ≤ (4 * H ^ 2) * (2 * H ^ 2) := mul_le_mul s hi (inv_pos.2 hp).le (by positivity)
      _ ≤ _ := by nlinarith [pow_nonneg h0 4]

variable {F : Type} [Field F] [NumberField F]

theorem sl_bound (k : ℕ) (f : Hn F → ℂ) (hf : Gr f) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ (x : GL (Fin 2) (InfinitePlace F → ℝ)) (H : ℝ), Pos x → 1 ≤ H → (∀ i j v, |x i j v| ≤ H) →
      (∀ i j v, |(x⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) i j v| ≤ H) →
      ‖sl k x f fun _ => UpperHalfPlane.I‖ ≤ C * (2 * H) ^ N := by
  obtain ⟨C, A, hC⟩ := hf
  set n := (Finset.univ : Finset (InfinitePlace F)).card with hnc
  refine ⟨|C|, 2 * n * k + n * k + 4 * n * A, abs_nonneg _, fun x H hp hH hx hy => ?_⟩
  have hb := fun v => place_bound (cmp v x) (by rw [cmp_det]; exact hp v) H (fun i j => hx i j v)
    (fun i j => by rw [← map_inv]; exact hy i j v)
  set K := 2 * H
  have hK : 1 ≤ K := by simp only [K]; linarith
  have h1 : (∏ v, |(x : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) ≤ (K ^ 2) ^ n := by
    rw [hnc, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v _ => by rw [← cmp_det]; exact (hb v).1
  have h1' : (∏ v, |(x : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) ^ ((k : ℝ) / 2) ≤ K ^ (2 * n * k) := by
    calc _ ≤ ((K ^ 2) ^ n) ^ ((k : ℝ) / 2) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => abs_nonneg _) h1 (by positivity)
      _ ≤ ((K ^ 2) ^ n) ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (one_le_pow₀ hK)) (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)
      _ = _ := by rw [Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_assoc]
  have h2 : ‖(∏ v, denom (cmp v x) (UpperHalfPlane.I))⁻¹ ^ k‖ ≤ K ^ (n * k) := by
    rw [norm_pow, pow_mul, norm_inv, norm_prod, ← Finset.prod_inv_distrib]
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun v _ => by positivity) ?_ k
    rw [hnc, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun v _ => by positivity) fun v _ => (hb v).2.1
  have h3 : ‖f (act x fun _ => UpperHalfPlane.I)‖ ≤ |C| * K ^ (4 * n * A) := by
    refine (hC _).trans ?_
    have hn : ∀ v, 0 ≤ (1 + ‖((act x (fun _ => UpperHalfPlane.I) v : ℍ) : ℂ)‖ ^ 2) / (act x (fun _ => UpperHalfPlane.I) v).im :=
      fun v => div_nonneg (by positivity) (im_pos _).le
    refine mul_le_mul (le_abs_self _) ?_ (pow_nonneg (Finset.prod_nonneg fun v _ => hn v) _) (abs_nonneg _)
    rw [pow_mul, pow_mul]
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun v _ => hn v) ?_ A
    rw [hnc, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun v _ => hn v) fun v _ => (hb v).2.2
  have hK0 : 0 ≤ K := by linarith
  simp only [sl, sl0]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (Real.rpow_nonneg (Finset.prod_nonneg fun v _ => abs_nonneg _) _)]
  calc _ ≤ K ^ (2 * n * k) * (K ^ (n * k) * (|C| * K ^ (4 * n * A))) :=
        mul_le_mul h1' (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
    _ = _ := by rw [pow_add, pow_add]; ring

theorem one_le_height (y : GL (Fin 2) (InfinitePlace F → ℝ)) : 1 ≤ TR.height y := by
  unfold TR.height
  linarith [norm_nonneg (TR.toL y.val), norm_nonneg (TR.toL (y⁻¹).val)]

theorem entry_le_norm (y : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)) (i j : Fin 2) (v : InfinitePlace F) :
    |y i j v| ≤ ‖TR.toL y‖ :=
  (norm_le_pi_norm (TR.toL y i j) v).trans ((norm_le_pi_norm (TR.toL y i) j).trans (norm_le_pi_norm (TR.toL y) i))

theorem entry_le_height (y : GL (Fin 2) (InfinitePlace F → ℝ)) (i j : Fin 2) (v : InfinitePlace F) :
    |y i j v| ≤ TR.height y := by
  unfold TR.height
  linarith [entry_le_norm y.val i j v, norm_nonneg (TR.toL (y⁻¹).val)]

theorem inv_entry_le_height (y : GL (Fin 2) (InfinitePlace F → ℝ)) (i j : Fin 2) (v : InfinitePlace F) :
    |(y⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) i j v| ≤ TR.height y := by
  unfold TR.height
  linarith [entry_le_norm (y⁻¹).val i j v, norm_nonneg (TR.toL y.val)]

theorem mul_entry_le (x y : GL (Fin 2) (InfinitePlace F → ℝ)) (a b : ℝ) (hx : ∀ i j v, |x i j v| ≤ a)
    (hy : ∀ i j v, |y i j v| ≤ b) (i j : Fin 2) (v : InfinitePlace F) :
    |(x * y : GL (Fin 2) (InfinitePlace F → ℝ)) i j v| ≤ 2 * a * b := by
  have e : (x * y : GL (Fin 2) (InfinitePlace F → ℝ)) i j v = x i 0 v * y 0 j v + x i 1 v * y 1 j v := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have ha : 0 ≤ a := (abs_nonneg _).trans (hx i j v)
  have h1 : |x i 0 v * y 0 j v| ≤ a * b := by rw [abs_mul]; exact mul_le_mul (hx _ _ _) (hy _ _ _) (abs_nonneg _) ha
  have h2 : |x i 1 v * y 1 j v| ≤ a * b := by rw [abs_mul]; exact mul_le_mul (hx _ _ _) (hy _ _ _) (abs_nonneg _) ha
  rw [e]
  linarith [abs_add_le (x i 0 v * y 0 j v) (x i 1 v * y 1 j v)]

theorem sl_mul_bound (k : ℕ) (f : Hn F → ℂ) (hf : Gr f) (t : GL (Fin 2) (InfinitePlace F → ℝ)) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ y : GL (Fin 2) (InfinitePlace F → ℝ), Pos (t * y) →
      ‖sl k (t * y) f fun _ => UpperHalfPlane.I‖ ≤ C * TR.height y ^ N := by
  obtain ⟨C, N, hC, h⟩ := sl_bound k f hf
  have ht := one_le_height t
  refine ⟨C * (4 * TR.height t) ^ N, N, by positivity, fun y hp => ?_⟩
  have hy := one_le_height y
  have := h (t * y) (2 * TR.height t * TR.height y) hp (by nlinarith)
    (mul_entry_le t y _ _ (entry_le_height t) (entry_le_height y)) fun i j v => by
      rw [mul_inv_rev]
      exact (mul_entry_le _ _ _ _ (inv_entry_le_height y) (inv_entry_le_height t) i j v).trans_eq (by ring)
  refine this.trans_eq ?_
  rw [mul_assoc C, ← mul_pow]
  congr 2
  ring

theorem det_ne_zero (v : InfinitePlace F) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v ≠ 0 := by
  rw [← cmp_det]; exact Units.ne_zero _

theorem pos_of_sign (t y y' : GL (Fin 2) (InfinitePlace F → ℝ)) (hp : Pos (t * y))
    (hs : ∀ v, 0 < y.val.det v ↔ 0 < y'.val.det v) : Pos (t * y') := by
  intro v
  have h := hp v
  rw [det_mul_apply] at h ⊢
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos h1 ((hs v).1 h2)
  · refine mul_pos_of_neg_of_neg h1 (lt_of_le_of_ne (not_lt.1 fun h3 => ?_) (det_ne_zero v y'))
    exact lt_asymm h2 ((hs v).2 h3)

theorem lift_growth : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Gr (Ψ g)) → IsLift k Ψ φ → ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * TR.infGL F 2 y)‖ ≤ C * TR.height y ^ N := by
  intro F _ _ _ k Ψ φ hgr hl g
  classical
  rw [← TR.infGL_mul_finGL g]
  set h := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set u := Matrix.GeneralLinearGroup.map (pFin F) g
  have key : ∀ s : InfinitePlace F → Prop, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ y : GL (Fin 2) (InfinitePlace F → ℝ),
      (∀ v, 0 < y.val.det v ↔ s v) →
      ‖φ (TR.infGL F 2 h * finGL F 2 u * TR.infGL F 2 y)‖ ≤ C * TR.height y ^ N := by
    intro s
    by_cases hs : ∃ y₀ : GL (Fin 2) (InfinitePlace F → ℝ), ∀ v, 0 < y₀.val.det v ↔ s v
    · obtain ⟨y₀, h₀⟩ := hs
      obtain ⟨τ, hτ⟩ := (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2 (h * y₀)
      rw [← mul_assoc] at hτ
      obtain ⟨C, N, hC, hb⟩ := sl_mul_bound k (Ψ (toFin τ * u)) (hgr _) (toInf τ * h)
      refine ⟨C, N, hC, fun y hy => ?_⟩
      have hp : Pos (toInf τ * h * y) := pos_of_sign _ y₀ y hτ fun v => (h₀ v).trans (hy v).symm
      have e : ratGL F 2 τ * (TR.infGL F 2 h * finGL F 2 u * TR.infGL F 2 y) =
          TR.infGL F 2 (toInf τ * h * y) * finGL F 2 (toFin τ * u) := by
        rw [(GlobalTheory.T.rational_GL2_infinite_finite_factor F τ).1]
        exact TR.ga_ext (by simp [mul_assoc]) (by simp)
      rw [← hl.1 τ, e, hl.2 _ hp]
      exact hb y hp
    · exact ⟨0, 0, le_rfl, fun y hy => absurd ⟨y, hy⟩ hs⟩
  choose C N hC hb using key
  refine ⟨∑ s, C s, ∑ s, N s, fun y => (hb (fun v => 0 < y.val.det v) y fun _ => Iff.rfl).trans ?_⟩
  have hy := one_le_height y
  exact mul_le_mul (Finset.single_le_sum (fun s _ => hC s) (Finset.mem_univ _))
    (pow_le_pow_right₀ hy (Finset.single_le_sum (fun s _ => Nat.zero_le (N s)) (Finset.mem_univ _)))
    (by positivity) (Finset.sum_nonneg fun s _ => hC s)

end GlobalTheory.HilbertThetaSeries.LiftGrowth

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_lift_has_moderate_growth : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Gr (Ψ g)) → IsLift k Ψ φ → ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * TR.infGL F 2 y)‖ ≤ C * TR.height y ^ N := by
  first | exact @GlobalTheory.HilbertThetaSeries.LiftGrowth.lift_growth | exact GlobalTheory.HilbertThetaSeries.LiftGrowth.lift_growth | (intros; apply GlobalTheory.HilbertThetaSeries.LiftGrowth.lift_growth <;> assumption)
