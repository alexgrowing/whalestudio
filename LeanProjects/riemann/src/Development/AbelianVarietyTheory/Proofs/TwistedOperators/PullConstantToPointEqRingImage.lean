import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullConst

theorem pull_const_apply : ∀ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {Y : Scheme.{0}} (q : Y ⟶ Sp T) (U : Y.Opens) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U), w ≫ q = spMap χ → ∀ a : T, (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := by
  intro T Ω _ _ χ Y q U w h hwq a
  have key : q.appLE ⊤ U le_top ≫ w.appLE U ⊤ h = (w ≫ q).appTop :=
    (Scheme.Hom.appLE_comp_appLE w q ⊤ U ⊤ le_top h).trans
      (Scheme.Hom.appLE_eq_app (f := w ≫ q) (U := ⊤))
  have k1 : (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) =
      (w ≫ q).appTop.hom (toΓ T a) := by
    have := congrArg (fun g => g.hom (toΓ T a)) key
    simpa only [CommRingCat.comp_apply] using this
  refine k1.trans ?_
  rw [hwq]
  have h3 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ)
  have h4 := congrArg (fun g => g.hom a) h3
  simp only [CommRingCat.comp_apply] at h4
  exact h4.symm

end GlobalTheory.PullConst
