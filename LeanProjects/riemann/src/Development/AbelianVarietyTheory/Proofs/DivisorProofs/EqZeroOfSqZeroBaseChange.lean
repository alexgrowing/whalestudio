import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleOneOnThickening
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulEqZeroOfAppEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CechPic

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res h1 (res h2 x) = res (h1.trans h2) x :=
  unit_ext fun y hy => by rw [gm_res _ y _ hy, gm_res _ y _ (h1 hy), gm_res _ y _ hy]

theorem app_restrict {X X₀ : Scheme.{0}} (i : X₀ ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (i.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (X₀.presheaf.map (homOfLE (fun y (hy : y ∈ i ⁻¹ᵁ V) => (h hy : i y ∈ U))).op).hom ((i.app U).hom x) := by
  have e := congrArg (fun q => q.hom x) (i.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

end GlobalTheory.CechPic
