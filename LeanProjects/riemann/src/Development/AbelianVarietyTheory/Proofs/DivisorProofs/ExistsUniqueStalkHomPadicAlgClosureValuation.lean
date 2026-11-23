import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ValPt

theorem exists_unique_stalk_hom : ∀ (X : Scheme.{0}) (x : X) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x → ∃ φ : X.presheaf.stalk x →+* OO p, IsLocalHom φ ∧ spMap φ ≫ X.fromSpecStalk x = y ∧ ∀ g : X.presheaf.stalk x →+* OO p, spMap g ≫ X.fromSpecStalk x = y → g = φ := by
  intro X x p _ y hy
  subst hy
  refine ⟨(Scheme.stalkClosedPointTo y).hom, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y, ?_⟩
  intro g hg
  have hpt : (X.fromSpecStalk (y (cPt p))) ((spMap g) (cPt p)) =
      (X.fromSpecStalk (y (cPt p))) (closedPoint (X.presheaf.stalk (y (cPt p)))) := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact congrArg (fun f : Sp (OO p) ⟶ X => f (cPt p)) hg
  have hinj : Function.Injective (X.fromSpecStalk (y (cPt p))) :=
    (X.fromSpecStalk (y (cPt p))).isEmbedding.injective
  have hloc : IsLocalHom g := by
    rw [isLocalHom_iff_comap_closedPoint]
    exact hinj hpt
  have e2 := (SpecToEquivOfLocalRing X (CommRingCat.of (OO p))).symm.injective
    (a₁ := ⟨y (cPt p), CommRingCat.ofHom g, hloc⟩)
    (a₂ := ⟨y (cPt p), Scheme.stalkClosedPointTo y, inferInstance⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
        exact hg.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at e3
  exact congrArg CommRingCat.Hom.hom e3

end GlobalTheory.ValPt
