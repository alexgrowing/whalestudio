import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterEqOneOfDescendedLineBundleTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem exists_pullTop_of_isPullback : ∀ {S X : Scheme.{0}} (A Z : Over S) [GrpObj A], IsAbelianScheme A → ∀ (p : X ⟶ A.left) (q : X ⟶ Z.left), IsPullback p q A.hom Z.hom → ∀ D : Γ(X, ⊤)ˣ, ∃ c : Γ(Z.left, ⊤)ˣ, GlobalTheory.CharKer.pullTop q c = D := by
  intro S X A Z _ hA p q h D
  obtain ⟨c, hc⟩ := exists_pullTop_snd A Z hA (pullTop h.isoPullback.inv D)
  refine ⟨c, ?_⟩
  have h₁ : h.isoPullback.hom ≫ (snd A Z).left = q := h.isoPullback_hom_snd
  have h₂ := congrArg (pullTop h.isoPullback.hom) hc
  rw [← h₁]
  refine (pullTop_pullTop_comp _ _ c).symm.trans (h₂.trans ?_)
  rw [pullTop_pullTop_comp, Iso.hom_inv_id]
  rfl

end GlobalTheory.CharKer
