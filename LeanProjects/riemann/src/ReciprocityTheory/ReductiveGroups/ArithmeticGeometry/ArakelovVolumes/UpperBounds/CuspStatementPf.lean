import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HolomorphicPeriodicityExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms

noncomputable section

namespace FactorialDivisibilityBounds

theorem abel_bound (a L : ℕ → ℝ) (p r : ℕ) (hL : ∀ k ≤ r, L k ≤ L p)
    (hgap : ∀ k, 1 ≤ k → k < r → k ≠ p → a k ≤ a (k - 1)) :
    ∀ n, 1 ≤ n → n ≤ r → ∑ k ∈ Finset.range n, a k * (L (k + 1) - L k) ≤
      a (n - 1) * L n - a 0 * L 0 + (a 0 - a (n - 1)) * L p := by
  intro n hn1 hnr
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [zero_add, Finset.sum_range_one, Nat.sub_self, sub_self, zero_mul, add_zero]
      linarith
    · have ih' := ih hpos (by omega)
      rw [Finset.sum_range_succ]
      have hLn := hL n (by omega)
      have key : (a (n - 1) - a n) * (L n - L p) ≤ 0 := by
        by_cases hnp : n = p
        · rw [hnp, sub_self, mul_zero]
        · have h1 := hgap n hpos (by omega) hnp
          exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      simp only [Nat.add_sub_cancel]
      nlinarith [ih', key]

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

def rfac (la : Wt X.Ψ r) (x y : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
    ‖dmin X.Gm y τ i.succ / dmin X.Gm y τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

theorem nfac_div (la : Wt X.Ψ r) (x y : Frame X.Ψ r) :
    X.nfac la x / X.nfac la y = ∏ τ, rfac X la x y τ := by
  rw [Data.nfac, Data.nfac, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun τ _ => (Finset.prod_div_distrib _ _).symm

def rho (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : ℕ) : ℝ :=
  1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i

section Flow

variable (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
  (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) (τ : X.Ψ)
include he hx

theorem dmin_flow' (j : Fin (r + 1)) :
    dmin X.Gm (X.flowV e s x) τ j = dmin X.Gm x τ j * ((rho X e s x τ j : ℝ) : ℂ) := by
  rw [dmin_eq, dmin_eq]
  exact dmin_flow X hx e τ (he τ).1 s j _

theorem dmin_ne' (j : Fin (r + 1)) : dmin X.Gm x τ j ≠ 0 := fun h0 => by
  have := (hx τ).2 j
  rw [h0, Complex.zero_re, mul_zero] at this
  exact lt_irrefl _ this

include hT in
theorem rho_pos : ∀ i ≤ r, 0 < rho X e s x τ i := fun i hi => by
  have h1 := (hT τ).2 ⟨i, Nat.lt_succ_of_le hi⟩
  rw [dmin_flow' X e he hx s τ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, ← mul_assoc] at h1
  exact (mul_pos_iff_of_pos_left ((hx τ).2 ⟨i, Nat.lt_succ_of_le hi⟩)).mp h1

include hT in
theorem rfac_eq (la : Wt X.Ψ r) :
    rfac X la x (X.flowV e s x) τ = Real.exp (∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i))) := by
  have hρ := rho_pos X e he hx s hT τ
  have hfac : ∀ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
      ‖dmin X.Gm (X.flowV e s x) τ i.succ / dmin X.Gm (X.flowV e s x) τ i.castSucc‖ ^
        (-(la τ i : ℝ) / 2) =
      Real.exp ((la τ i : ℝ) / 2 *
        (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i))) := by
    intro i
    have hρ1 := hρ ((i : ℕ) + 1) i.2
    have hρ0 := hρ i i.2.le
    have hN : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
      norm_pos_iff.mpr (div_ne_zero (dmin_ne' X e he hx τ _) (dmin_ne' X e he hx τ _))
    rw [dmin_flow' X e he hx s τ, dmin_flow' X e he hx s τ, Fin.val_succ, Fin.val_castSucc]
    have hn : ‖dmin X.Gm x τ i.succ * ((rho X e s x τ ((i : ℕ) + 1) : ℝ) : ℂ) /
        (dmin X.Gm x τ i.castSucc * ((rho X e s x τ i : ℝ) : ℂ))‖ =
        ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ *
          (rho X e s x τ ((i : ℕ) + 1) / rho X e s x τ i) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hρ1.le, Real.norm_of_nonneg hρ0.le, norm_div]
      field_simp
    rw [hn, Real.mul_rpow hN.le (div_pos hρ1 hρ0).le,
      div_mul_cancel_left₀ (Real.rpow_pos_of_pos hN _).ne', ← Real.rpow_neg (div_pos hρ1 hρ0).le,
      Real.rpow_def_of_pos (div_pos hρ1 hρ0), Real.log_div hρ1.ne' hρ0.ne']
    congr 1
    ring
  rw [rfac, Finset.prod_congr rfl fun i _ => hfac i, ← Real.exp_sum]

include hT in
theorem rfac_of_zero (la : Wt X.Ψ r) (hs : s τ = 0) : rfac X la x (X.flowV e s x) τ = 1 := by
  rw [rfac_eq X e he hx s hT τ la]
  have h1 : ∀ i, rho X e s x τ i = 1 := fun i => by simp [rho, hs]
  simp [h1]

include hT in
theorem rfac_le (la : Wt X.Ψ r) (hs : 0 ≤ (s τ).im) (hp0 : 0 < X.p0) (hp0r : X.p0 < r)
    (hgap : ∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i)
    (hpair : ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ i0 < la τ i1) :
    rfac X la x (X.flowV e s x) τ ≤
      Real.exp (-(1 / 2) * Real.log (1 + (s τ).im / X.ttV e x τ)) := by
  rw [rfac_eq X e he hx s hT τ la]
  apply Real.exp_le_exp.mpr
  have hρ := rho_pos X e he hx s hT τ
  have hsg := hsg_of X hx τ
  have hb : 0 ≤ 2 * X.c τ * (s τ).im := by have := c_pos X τ; positivity
  have hmb : ∀ i ≤ r, 0 ≤ mN τ.1 X.Gm (mat x τ) (e τ) i ∧
      mN τ.1 X.Gm (mat x τ) (e τ) i ≤ mN τ.1 X.Gm (mat x τ) (e τ) X.p0 :=
    fun i hi => mN_bounds (hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 hsg (e τ) (he τ).1 i hi
  set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
  have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
  have hLr : L r = 0 := by
    simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
  have hLle : ∀ k ≤ r, L k ≤ L X.p0 := fun k hk => by
    apply Real.log_le_log (hρ k hk)
    simp only [rho]
    nlinarith [(hmb k hk).2]
  have hLp : 0 ≤ L X.p0 := by
    apply Real.log_nonneg
    simp only [rho]
    nlinarith [(hmb X.p0 X.p0_le).1]
  set a : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) / 2 else 0 with ha
  have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
      ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => a k * (L (k + 1) - L k)) r]
    exact Finset.sum_congr rfl fun i _ => by simp only [a, L, dif_pos i.2]
  have hgap' : ∀ k, 1 ≤ k → k < r → k ≠ X.p0 → a k ≤ a (k - 1) := by
    intro k hk1 hkr hkp
    simp only [a, dif_pos hkr, dif_pos (show k - 1 < r by omega)]
    have := hgap ⟨k - 1, by omega⟩ ⟨k, hkr⟩ (by simp; omega) hkp
    have : (la τ ⟨k, hkr⟩ : ℝ) ≤ la τ ⟨k - 1, by omega⟩ := by exact_mod_cast this
    linarith
  have hab := abel_bound a L X.p0 r hLle hgap' r (by omega) le_rfl
  rw [hL0, hLr] at hab
  have hpa : a 0 - a (r - 1) ≤ -(1 / 2) := by
    simp only [a, dif_pos (show 0 < r by omega), dif_pos (show r - 1 < r by omega)]
    have := hpair ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
    have : (la τ ⟨0, by omega⟩ : ℝ) + 1 ≤ la τ ⟨r - 1, by omega⟩ := by exact_mod_cast this
    linarith
  have hq : 1 + (s τ).im / X.ttV e x τ = rho X e s x τ X.p0 := by
    rw [Data.ttV, maj_eq X hx e τ (he τ).1, div_div_eq_mul_div, div_one]
    simp only [rho]
    ring
  rw [hsum, hq]
  have : (a 0 - a (r - 1)) * L X.p0 ≤ -(1 / 2) * L X.p0 :=
    mul_le_mul_of_nonneg_right hpa hLp
  show _ ≤ -(1 / 2) * L X.p0
  linarith

end Flow

end FactorialDivisibilityBounds

open FactorialDivisibilityBounds

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem cuspStatement_holds : CuspStatement (E := E) := by
  intro r X la τ0 hp0 hp0r hgap hpair P hP
  classical
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  obtain ⟨C, hC⟩ := hP.2
  have hiso : X.IsIsoV (X.embV ξ) := fun τ =>
    ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  set G := X.fj la ξ 0 P with hG
  have hGb : ∀ y ∈ X.dom, ‖G y‖ * X.nfac la y ≤ C := fun y hy =>
    FlowCoefficientBounds.fj_bound X la P C hC hξ 0 hy
  have hGd : DifferentiableOn ℂ G X.dom := CuspCoefficientFlow.fj_diffOn X la P hP hξ 0
  have hreal : ∀ s : X.Ψ → ℝ, G (X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, (0 : X.Ψ → ℂ) τ * s τ) * G x := by
    intro s
    have := X.fj_flow_real la ξ hξ 0 P hP.1 ⟨C, hC⟩ x hx s
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul] at this ⊢
    exact this
  have hcx := holomorphic_periodicity_extension r X (X.embV ξ) hiso G hGd 0 x hx hreal
  by_contra hne
  have hN := FlowCoefficientBounds.nfac_pos X hx la
  have hA : 0 < ‖G x‖ * X.nfac la x := mul_pos (norm_pos_iff.mpr hne) hN
  have hmaj := maj_eq X hx (X.embV ξ) τ0 (hiso τ0).1
  have hmpos := mN_pos (hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1 (hsg_of X hx τ0)
    (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2
  have htt : 0 < X.ttV (X.embV ξ) x τ0 := by
    rw [Data.ttV, hmaj]
    have := c_pos X τ0
    positivity
  set M : ℝ := |Real.log (C / (‖G x‖ * X.nfac la x))| + 1 with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := X.ttV (X.embV ξ) x τ0 * (Real.exp (2 * M) - 1) with ht
  have ht0 : 0 < t := mul_pos htt (by linarith [Real.add_one_lt_exp (show (2 * M) ≠ 0 by positivity)])
  let s : X.Ψ → ℂ := fun τ => if τ = τ0 then I * t else 0
  have hs0 : (s τ0).im = t := by simp [s]
  have hdom : X.flowV (X.embV ξ) s x ∈ X.dom := by
    refine (flowDomainCriterion_holds r X _ hiso x hx s).1.mpr fun τ => ?_
    by_cases h : τ = τ0
    · subst h
      rw [hs0]
      have : 0 < t / X.ttV (X.embV ξ) x τ := div_pos ht0 htt
      linarith
    · simp [s, h]
  have hq : 1 + (s τ0).im / X.ttV (X.embV ξ) x τ0 = Real.exp (2 * M) := by
    rw [hs0, ht, mul_div_cancel_left₀ _ htt.ne']
    ring
  have hratio : X.nfac la x / X.nfac la (X.flowV (X.embV ξ) s x) ≤ Real.exp (-M) := by
    rw [nfac_div, Finset.prod_eq_single τ0 (fun τ _ hτ => rfac_of_zero X _ hiso hx s hdom τ la
      (by simp [s, hτ])) (fun h => absurd (Finset.mem_univ τ0) h)]
    refine (rfac_le X _ hiso hx s hdom τ0 la (by rw [hs0]; exact ht0.le) hp0 hp0r (hgap) hpair).trans
      (le_of_eq ?_)
    rw [hq, Real.log_exp]
    congr 1
    ring
  have hNT := FlowCoefficientBounds.nfac_pos X hdom la
  have hGT : G (X.flowV (X.embV ξ) s x) = G x := by
    rw [hcx s hdom]
    simp
  have h1 : X.nfac la x ≤ X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M) := by
    rw [div_le_iff₀ hNT] at hratio
    rw [mul_comm]
    exact hratio
  have h2 : ‖G x‖ * X.nfac la x ≤ C * Real.exp (-M) := by
    calc ‖G x‖ * X.nfac la x ≤ ‖G x‖ * (X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖G (X.flowV (X.embV ξ) s x)‖ * X.nfac la (X.flowV (X.embV ξ) s x)) *
          Real.exp (-M) := by rw [hGT]; ring
      _ ≤ C * Real.exp (-M) := mul_le_mul_of_nonneg_right (hGb _ hdom) (Real.exp_pos _).le
  rcases le_or_gt C 0 with hC0 | hC0
  · have : C * Real.exp (-M) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (Real.exp_pos _).le
    linarith
  · have hlt : Real.log (C / (‖G x‖ * X.nfac la x)) < M := by
      have := le_abs_self (Real.log (C / (‖G x‖ * X.nfac la x)))
      linarith
    have h3 : C / (‖G x‖ * X.nfac la x) < Real.exp M := by
      rw [← Real.exp_log (div_pos hC0 hA)]
      exact Real.exp_lt_exp.mpr hlt
    have h4 : C * Real.exp (-M) < ‖G x‖ * X.nfac la x := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
      rw [div_lt_iff₀ hA] at h3
      linarith
    linarith

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
