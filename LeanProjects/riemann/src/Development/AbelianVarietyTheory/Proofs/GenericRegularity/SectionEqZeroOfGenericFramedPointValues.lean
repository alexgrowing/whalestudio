import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem evR_eq_map_of_test_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {g : Rul Xo c} (hg : g ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] (p : TRing c.F)
    (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R) (w : FrPt Xo c S) (hw : FrMap φ y w) :
    evR Xo c g w = φ (g p y) := by
  have h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hw⟩
  unfold evR evalAt
  rw [dif_pos h]
  exact hL.wd g hg.1 S _ p _ φ _ y w h.choose_spec.choose_spec.choose_spec hw

theorem sec_eq_zero_of_generic_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec Xo c a n, (∀ Z, evC h Z g = 0) → g = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA a n g hg h0
  have hfield : ∀ (L : Type) [Field L] [Algebra c.F L] (w : FrPt Xo c L), evR Xo c g w = 0 := by
    intro L _ _ w
    obtain ⟨C, ψ, z, t', hz, hb⟩ := hA L w
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
    have h1 : evR Xo c g C.yg = 0 := by
      rw [hL.wt a n g hg _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor]
      have := h0 C.Z
      unfold evC at this
      rw [this, mul_zero]
    have h2 : χ (g q y₀) = 0 := by
      rw [evR_eq_map_of_test_point hL hg q (C.R.val.comp χ) y₀ C.yg
        (frMap_trans _ _ _ _ _ _ _ _ hy₀ C.gen)] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c g z = 0 := by
      rw [evR_eq_map_of_test_point hL hg q (ψ.comp χ) y₀ z (frMap_trans _ _ _ _ _ _ _ _ hy₀ hz), AlgHom.comp_apply,
        h2, map_zero]
    rw [hL.wt a n g hg _ t' _ _ (hL.test _ _) (hL.test _ _) hb, h3, mul_zero]
  funext p y
  have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  show g p y = 0
  refine IsNilpotent.eq_zero ?_
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : p.R →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F p.R P.ResidueField
  obtain ⟨w, hw⟩ := hL.bc _ _ φ y
  have h4 := hfield _ w
  rw [evR_eq_map_of_test_point hL hg p φ y w hw] at h4
  exact Ideal.algebraMap_residueField_eq_zero.1 h4

end GlobalTheory.Reg
