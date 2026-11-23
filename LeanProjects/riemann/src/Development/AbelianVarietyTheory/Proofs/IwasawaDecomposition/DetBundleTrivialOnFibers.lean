import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmpStOfSabExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFiberNormalReduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisPullbackCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetLieTrivializedByTangentBasisStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.DetTriv

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg

attribute [local instance] Over.cartesianMonoidalCategory

theorem detOm_trivial_of_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hY : (GlobalTheory.FlagMod.detOm Y).IsLB), Y.jQ ≫ ρ = X.jQ →
    ∀ (W : Scheme.{0}) (K : Type) [Field K] (g : W ⟶ gen Y) (a : W ⟶ Sp K) (y0 : Sp K ⟶ gen X), g ≫ ρ = a ≫ y0 →
    GlobalTheory.CechPic.pull (g ≫ genι Y) (GlobalTheory.CechPic.cls _ hY) = 0 := by
  intro E _ _ _ H D l Xo c X Y ρ hY hρ W K _ g a y0 hga
  have hLY : (detLie Y).IsLB := isLB_of_ev _ hY.cover fun i j k _ _ z => ev_detChg_mul i j k z
  obtain ⟨t₀, n₁, n₂, -⟩ := cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt homExtNormal) E H D l Xo c
    (𝓞 c.F) c.F (algebraMap (𝓞 c.F) c.F) (RingHom.id c.F) X Y ρ hρ
    (GlobalTheory.GenFibre.gen_normal_reduced_noetherian E H D l Xo c Y).1
  obtain ⟨tK, ⟨mK⟩⟩ := exists_sabMap_pull (y0 ≫ genι X) X.t
  obtain ⟨tW, ⟨mW⟩⟩ := exists_sabMap_pull g t₀
  obtain ⟨mY, -⟩ := GlobalTheory.LevelCover.sab_comp mW n₁ (e := g ≫ genι Y) rfl
  obtain ⟨mX, -⟩ := GlobalTheory.LevelCover.sab_comp mW n₂ (e := g ≫ ρ ≫ genι X) rfl
  obtain ⟨mA, -⟩ := GlobalTheory.LevelCover.sab_cancel mK mX a ((reassoc_of% hga) (genι X)).symm
  obtain ⟨d, B, hB⟩ := GlobalTheory.T.tangent_basis_pullback_compatible E H K tK
  have h0 := GlobalTheory.T.det_lie_trivialized_by_tangent_basis E H D l Xo c c.F (RingHom.id c.F) Y hLY W (g ≫ genι Y) tW.G _ mY.cart d
    (fun S _ x => (B S (x ≫ a)).map (GlobalTheory.PolFin.tanEquiv mA.cart x).symm) (fun S S' _ _ φ x x' e j => by
      have e' : spMap φ ≫ x ≫ a = x' ≫ a := by rw [← Category.assoc, e]
      simp only [Module.Basis.map_apply]
      rw [LinearEquiv.eq_symm_apply, ← GlobalTheory.PolFin.tanPull_tanEquiv mA.cart φ e e', LinearEquiv.apply_symm_apply]
      exact hB S S' φ _ _ e' j)
  rw [show GlobalTheory.CechPic.cls (detOm Y) hY = -GlobalTheory.CechPic.cls _ hLY from GlobalTheory.CechPic.cls_dual hLY hY, map_neg, h0,
    neg_zero]

end GlobalTheory.DetTriv
