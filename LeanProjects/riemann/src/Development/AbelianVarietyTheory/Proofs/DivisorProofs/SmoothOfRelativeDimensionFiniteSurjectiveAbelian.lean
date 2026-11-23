import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodOfFiniteSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDimField

theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (K : Type) [Field K] [IsAlgClosed K]
    (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' →
    IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g A'.hom := by
  intro K _ _ A A' _ _ g q hA hA' hfin hsurj hg
  have := hA.geomConnected
  have := hA'.geomConnected
  have := hA'.smooth
  have : ConnectedSpace A.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.hom) (𝟙 _) (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have : ConnectedSpace A'.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A'.hom) (𝟙 _) (𝟙 _) A'.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected A'.hom (Classical.arbitrary A'.left)
  have hw : q.left ≫ A'.hom = A.hom := Over.w q
  have hg' : SmoothOfRelativeDimension g (q.left ≫ A'.hom) := by rw [hw]; exact hg
  have e := GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := K) q.left A'.hom hg' hm
  subst e
  exact hm

end GlobalTheory.FiniteSurjDimField
