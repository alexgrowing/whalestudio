import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem isGVal_unique' {F : Type} [Field F] [NumberField F] {k : ℕ}
    {L : _root_.GlobalTheory.HilbFam.Lat F} {b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ} {G G' : ℂ}
    (h : _root_.GlobalTheory.HilbFam.IsGVal k L b a G)
    (h' : _root_.GlobalTheory.HilbFam.IsGVal k L b a G') : G = G' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨h₁', h₂'⟩ := h'
  by_cases hk : k = 2
  · subst hk
    obtain ⟨H, hH, hsum, rfl⟩ := h₂ rfl
    obtain ⟨H', hH', hsum', rfl⟩ := h₂' rfl
    have hU : IsOpen {σ : ℂ | -1 / 2 < σ.re} := isOpen_lt continuous_const Complex.continuous_re
    have hC : IsPreconnected {σ : ℂ | -1 / 2 < σ.re} := (convex_halfSpace_re_gt _).isPreconnected
    have hone : (1 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num
    have hzero : (0 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.zero_re]; norm_num
    have hev : H =ᶠ[nhds 1] H' := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with σ hσ
      exact (hsum σ hσ).unique (hsum' σ hσ)
    exact (hH.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hH'.analyticOnNhd hU) hC
      hone hev hzero
  · exact (h₁ hk).unique (h₁' hk)

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.gval_eq_of_isGVal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (G : ℂ),
    _root_.GlobalTheory.HilbFam.IsGVal k L b a G → _root_.GlobalTheory.HilbFam.gval k L b a = G := by
  intro F _ _ _ k L b a G hG
  have h : ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L b a G := ⟨G, hG⟩
  rw [_root_.GlobalTheory.HilbFam.gval, dif_pos h]
  exact isGVal_unique' h.choose_spec hG

end GlobalTheory.HilbFam
