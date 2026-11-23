import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.HeckeEx

theorem bddSec_tendsto_constTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, (∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom) ∧ Filter.Tendsto (fun t : ℝ => P (X.flow ξ (fun _ => Complex.I * t) x)) Filter.atTop (nhds (X.fj la ξ 0 P x)) := by
  intro E _ _ _ r X la P hP ξ hξ x hx
  have hdom : ∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom := fun t ht =>
    GlobalTheory.FjCauchy.flow_mem_dom X hξ hx _ fun τ => by
      have := GlobalTheory.FjCauchy.tt_pos X hξ hx τ
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, zero_add]
      linarith
  refine ⟨hdom, ?_⟩
  have hexp := m3bExp_holds (E := E) r X la P hP.1 ξ hξ x hx

  have hfac : ∀ (ν : X.Ψ → ℝ) (t : ℝ),
      Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (fun _ => Complex.I * (t : ℂ)) τ) =
        ((Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) : ℝ) : ℂ) := by
    intro ν t
    rw [Complex.ofReal_exp]
    congr 1
    have hs : ∑ τ, (ν τ : ℂ) * (Complex.I * (t : ℂ)) = (∑ τ, (ν τ : ℂ)) * (Complex.I * t) := by
      rw [Finset.sum_mul]
    simp only [hs]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  set F : ℝ → (X.Ψ → ℝ) → ℂ := fun t ν =>
    X.fj la ξ ν P x * Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (fun _ => Complex.I * (t : ℂ)) τ)
    with hF
  have hF' : ∀ t ν, F t ν = X.fj la ξ ν P x * ((Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) : ℝ) : ℂ) := by
    intro t ν; rw [hF]; dsimp only; rw [hfac]

  have hsum0 : Summable fun ν : X.Ψ → ℝ => X.fj la ξ ν P x := by
    have h := (hexp _ (hdom 0 le_rfl)).summable
    refine h.congr fun ν => ?_
    have := hF' 0 ν
    rw [hF] at this
    simp only [mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, _root_.mul_one] at this
    exact this
  have hbound : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖ := summable_norm_iff.mpr hsum0
  have hsign : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ := fun ν h =>
    BoundedSectionAlgebra.sign_of_bdd X moderateCoefficientPositivity_holds hP hξ ν hx h
  have hlim : Filter.Tendsto (fun t => ∑' ν, F t ν) Filter.atTop
      (nhds (∑' ν : X.Ψ → ℝ, if ν = 0 then X.fj la ξ 0 P x else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun ν => ?_) ?_
    · by_cases h0 : X.fj la ξ ν P x = 0
      · have : (if ν = 0 then X.fj la ξ 0 P x else 0) = 0 := by
          split_ifs with h; · subst h; exact h0
          · rfl
        rw [this]
        simp only [hF', h0, zero_mul]
        exact tendsto_const_nhds
      by_cases hν : ν = 0
      · subst hν
        simp only [hF', if_true, Finset.sum_const_zero, Pi.zero_apply, mul_zero, zero_mul, neg_zero,
          Real.exp_zero, Complex.ofReal_one, _root_.mul_one]
        exact tendsto_const_nhds
      · rw [if_neg hν]
        have hnn := hsign ν h0
        obtain ⟨τ0, hτ0⟩ : ∃ τ0, ν τ0 ≠ 0 := by
          by_contra hc; push_neg at hc; exact hν (funext hc)
        have hS : 0 < ∑ τ, ν τ :=
          Finset.sum_pos' (fun τ _ => hnn τ) ⟨τ0, Finset.mem_univ _, lt_of_le_of_ne (hnn τ0) (Ne.symm hτ0)⟩
        have hk : 0 < 4 * Real.pi * ∑ τ, ν τ := by positivity
        have he : Filter.Tendsto (fun t : ℝ => Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)))
            Filter.atTop (nhds 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hk)
        have := ((Complex.continuous_ofReal.tendsto 0).comp he).const_mul (X.fj la ξ ν P x)
        simp only [Complex.ofReal_zero, mul_zero] at this
        simp only [hF']
        exact this
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht ν
      rw [hF', norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      by_cases h0 : X.fj la ξ ν P x = 0
      · simp [h0]
      have hS : 0 ≤ ∑ τ, ν τ := Finset.sum_nonneg fun τ _ => hsign ν h0 τ
      have : Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ 4 * Real.pi * (∑ τ, ν τ) * t := by positivity
        linarith
      calc ‖X.fj la ξ ν P x‖ * Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t))
          ≤ ‖X.fj la ξ ν P x‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖X.fj la ξ ν P x‖ := _root_.mul_one _
  rw [tsum_ite_eq] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [hF]
  exact (hexp _ (hdom t ht)).tsum_eq

end GlobalTheory.HeckeEx
