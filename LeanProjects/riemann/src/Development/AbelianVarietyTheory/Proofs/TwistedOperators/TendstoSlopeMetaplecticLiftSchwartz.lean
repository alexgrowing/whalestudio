import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

open scoped Matrix

namespace GlobalTheory.RealWeil

theorem tendsto_slope_omS_schwartz :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] (pr : G →* Matrix.symplecticGroup l ℝ)
    (om : G →* (GlobalTheory.RealWeil.L2 l ≃ₗᵢ[ℂ] GlobalTheory.RealWeil.L2 l)) (omS : G →* (GlobalTheory.RealWeil.Sch l →L[ℂ] GlobalTheory.RealWeil.Sch l)),
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : GlobalTheory.RealWeil.L2 l),
      om g (GlobalTheory.RealWeil.rho w f) = GlobalTheory.RealWeil.rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) →
    (∀ (g : G) (f : GlobalTheory.RealWeil.Sch l), om g (f.toLp 2) = (omS g f).toLp 2) →
    ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
    (∀ f : GlobalTheory.RealWeil.Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((GlobalTheory.RealWeil.quad X f).toLp 2) 0) →
    ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (omS (γ t) f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (GlobalTheory.RealWeil.quad X f)) := by
  intro l _ _ G _ pr om omS h3 h4 X hX γ h0 hγ h6 f
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le (l := l) k n
  have key : ∀ r, Filter.Tendsto
      (fun t : ℝ => ‖schwartzToL2 l (A r (t⁻¹ • (omS (γ t) f - f) - quad X f))‖) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    intro r
    have h := hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_toLp_omS h3 h4 hX h0 hγ h6 (hA r) f)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    refine h.congr fun t => ?_
    have e : ∀ (B : Sch l →L[ℂ] L2 l) (u v w : Sch l) (s : ℝ), B (s • (u - v) - w) = s • (B u - B v) - B w := by
      intro B u v w s
      rw [B.map_sub, B.map_smul_of_tower, B.map_sub]
    have e1 : omS (γ 0) f = f := by rw [h0, omS.map_one]; rfl
    rw [zero_add, e1]
    exact congrArg norm (e ((schwartzToL2 l).comp (A r)) _ _ _ _).symm
  have hs := tendsto_finset_sum Finset.univ fun r _ => key r
  rw [Finset.sum_const_zero] at hs
  filter_upwards [hs.eventually (gt_mem_nhds hε)] with t ht
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  exact (hb _).trans_lt ht

end GlobalTheory.RealWeil
