import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isIso_of_finite_etale_of_existsUnique_lift (W S : Scheme.{0}) (w : W ⟶ S) (hf : IsFinite w)
    (he : Etale w) (hc : PreconnectedSpace S) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S)
    (hs : ∃! x : Sp Ω ⟶ W, x ≫ w = s) : IsIso w := by
  obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨x₀, hx₀, hu⟩ := hs
  have hsub : Subsingleton {x : Sp Ω ⟶ W // x ≫ w = s} :=
    ⟨fun a b => Subtype.ext ((hu a.1 a.2).trans (hu b.1 b.2).symm)⟩
  have hne : Nonempty {x : Sp Ω ⟶ W // x ≫ w = s} := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨_, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank w s z
  have h1 : w.finrank (s z) = 1 := by
    rw [← hcard, Nat.card_eq_one_iff_unique]
    exact ⟨hsub, hne⟩
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext y
  rw [Pi.one_apply, ← h1]
  exact (Scheme.Hom.isLocallyConstant_finrank w).apply_eq_of_preconnectedSpace y (s z)

end GlobalTheory.Mum
