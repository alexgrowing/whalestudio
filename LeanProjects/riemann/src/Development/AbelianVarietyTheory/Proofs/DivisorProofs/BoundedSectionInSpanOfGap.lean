import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf

open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds

noncomputable section

namespace GlobalTheory.SepCusp

theorem exists_threshold {r : ℕ} (p : ℕ) (w : Fin r → ℤ)
    (h : ∀ a b : Fin r, (a : ℕ) < p → p ≤ (b : ℕ) → w a < w b) :
    ∃ M : ℤ, (∀ a : Fin r, (a : ℕ) < p → w a ≤ M) ∧ ∀ b : Fin r, p ≤ (b : ℕ) → M + 1 ≤ w b := by
  classical
  by_cases hne : (Finset.univ.filter fun b : Fin r => p ≤ (b : ℕ)).Nonempty
  · obtain ⟨b0, hb0, hmin⟩ := Finset.exists_min_image _ w hne
    refine ⟨w b0 - 1, fun a ha => ?_, fun b hb => ?_⟩
    · have := h a b0 ha (Finset.mem_filter.mp hb0).2
      omega
    · have := hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      omega
  · obtain ⟨M, hM⟩ := (Set.finite_range w).bddAbove
    exact ⟨M, fun a _ => hM ⟨a, rfl⟩,
      fun b hb => absurd ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩ hne⟩

theorem sum_le_of_unimodal (a L : ℕ → ℝ) (p r : ℕ) (hp : p ≤ r) (M : ℝ) (h0 : L 0 = 0) (hr : L r = 0)
    (hup : ∀ k < p, L k ≤ L (k + 1)) (hdown : ∀ k, p ≤ k → k < r → L (k + 1) ≤ L k)
    (ha : ∀ k < p, a k ≤ M) (hb : ∀ k, p ≤ k → k < r → M + 1 / 2 ≤ a k) :
    ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) ≤ -(1 / 2) * L p := by
  rw [← Finset.sum_range_add_sum_Ico _ hp]
  have h1 : ∑ k ∈ Finset.range p, a k * (L (k + 1) - L k) ≤
      ∑ k ∈ Finset.range p, M * (L (k + 1) - L k) :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (ha k (Finset.mem_range.mp hk))
      (sub_nonneg.mpr (hup k (Finset.mem_range.mp hk)))
  have h2 : ∑ k ∈ Finset.Ico p r, a k * (L (k + 1) - L k) ≤
      ∑ k ∈ Finset.Ico p r, (M + 1 / 2) * (L (k + 1) - L k) :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonpos_right
      (hb k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2)
      (sub_nonpos.mpr (hdown k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2))
  rw [← Finset.mul_sum, Finset.sum_range_sub, h0] at h1
  rw [← Finset.mul_sum, Finset.sum_Ico_sub L hp, hr] at h2
  linarith

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

theorem rfac_le_of_sep (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) (τ : X.Ψ) (la : Wt X.Ψ r) (hs : 0 ≤ (s τ).im)
    (hsep : ∀ a b : Fin r, (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) :
    rfac X la x (X.flowV e s x) τ ≤
      Real.exp (-(1 / 2) * Real.log (1 + (s τ).im / X.ttV e x τ)) := by
  rw [rfac_eq X e he hx s hT τ la]
  apply Real.exp_le_exp.mpr
  have hρ := rho_pos X e he hx s hT τ
  have hsg := hsg_of X hx τ
  have hb : 0 ≤ 2 * X.c τ * (s τ).im := by have := c_pos X τ; positivity
  have hp := X.p0_le
  set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
  have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
  have hLr : L r = 0 := by
    simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
  have hup : ∀ k < X.p0, L k ≤ L (k + 1) := fun k hk => by
    apply Real.log_le_log (hρ k (by omega))
    simp only [rho]
    have := mN_up (hG_of X τ) X.p0 X.p0_le (mat x τ) hsg (e τ) (k + 1) hk k (Nat.le_succ k)
    nlinarith
  have hdown : ∀ k, X.p0 ≤ k → k < r → L (k + 1) ≤ L k := fun k hk hkr => by
    apply Real.log_le_log (hρ (k + 1) hkr)
    simp only [rho]
    have := mN_down (hG_of X τ) X.p0 (mat x τ) hsg (e τ) k hk (k + 1) (Nat.le_succ k) hkr
    nlinarith
  set a : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) / 2 else 0 with ha
  have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
      ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => a k * (L (k + 1) - L k)) r]
    exact Finset.sum_congr rfl fun i _ => by simp only [a, L, dif_pos i.2]
  obtain ⟨M, hM1, hM2⟩ := exists_threshold X.p0 (la τ) hsep
  have hq : 1 + (s τ).im / X.ttV e x τ = rho X e s x τ X.p0 := by
    rw [Data.ttV, maj_eq X hx e τ (he τ).1, div_div_eq_mul_div, div_one]
    simp only [rho]
    ring
  rw [hsum, hq]
  refine sum_le_of_unimodal a L X.p0 r hp ((M : ℝ) / 2) hL0 hLr hup hdown (fun k hk => ?_)
    (fun k hk hkr => ?_)
  · have hkr : k < r := by omega
    have h1 : (la τ ⟨k, hkr⟩ : ℝ) ≤ M := by exact_mod_cast hM1 ⟨k, hkr⟩ hk
    simp only [a, dif_pos hkr]
    linarith
  · have h1 : (M : ℝ) + 1 ≤ la τ ⟨k, hkr⟩ := by exact_mod_cast hM2 ⟨k, hkr⟩ hk
    simp only [a, dif_pos hkr]
    linarith

theorem mem_SS_of_sep_at (la : Wt X.Ψ r) (τ0 : X.Ψ) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    (hsep : ∀ a b : Fin r, (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ0 a < la τ0 b) :
    P ∈ X.SS la := by
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
    refine (rfac_le_of_sep X _ hiso hx s hdom τ0 la (by rw [hs0]; exact ht0.le) hsep).trans
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

theorem nonempty_type : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : NumberField.ComplexEmbedding.conjugate τ ∈ X.Ψ
  · exact ⟨⟨_, h⟩⟩
  · exact ⟨⟨τ, (X.cmType τ).mpr h⟩⟩

theorem mem_SS_of_sep (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    (hsep : ∀ (τ : X.Ψ) (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) :
    P ∈ X.SS la := by
  obtain ⟨τ0⟩ := nonempty_type X
  exact mem_SS_of_sep_at X la τ0 P hP (hsep τ0)

end GlobalTheory.SepCusp
