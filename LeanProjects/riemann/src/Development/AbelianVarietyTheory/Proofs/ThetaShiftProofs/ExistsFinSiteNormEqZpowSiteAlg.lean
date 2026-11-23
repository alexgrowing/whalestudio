import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteSiteAlg

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_finSite_norm_eq_zpow_siteAlg :
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)),
      (∃ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes ∧ OverLa w Tv.V io 1) ∧
      ∀ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes → OverLa w Tv.V io 1 →
        ∃ (Z : FinSite K₁ w) (ιT : Tv.Fr →+* Z.K), ιT.comp io = Z.ι ∧
          (∀ x : Tv.Fr, x ≠ 0 → ‖ιT x‖ = Z.r ^ vV Tv.V x) ∧ SiteAlg Z Tv ιT := by
  intro K₁ _ _ w
  obtain ⟨h1, h2⟩ := exists_finSite_siteAlg K₁ w
  refine ⟨h1, fun Tv io hfin ho => ?_⟩
  obtain ⟨Z, ιT, hc, hn, hs⟩ := h2 Tv io 1 hfin ho
  refine ⟨Z, ιT, hc, fun x hx => ?_, hs⟩
  have hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨y, hy⟩ := w.valuation_exists_uniformizer K₁
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have hv : vLa w y = 1 := by
    rw [vLa, hy, WithZero.log_exp, neg_neg]
  have e1 : ‖Z.ι y‖ = Z.r := by
    have := Z.norm_ι y hy0
    rw [this]
    change Z.r ^ vLa w y = Z.r
    rw [hv, zpow_one]
  have e2 : ‖ιT (algebraMap Tv.V Tv.Fr π)‖ = Z.r := by
    rw [← e1, ← hc, RingHom.comp_apply,
      norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hy0), ho.2 y, hv]
    simp
  rw [norm_map_eq_zpow_vV ιT hf hπ hx, e2]

end GlobalTheory.ArcQ
