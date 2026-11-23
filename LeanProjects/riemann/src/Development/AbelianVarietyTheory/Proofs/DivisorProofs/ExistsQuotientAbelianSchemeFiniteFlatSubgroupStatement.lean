import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_abelianScheme_finiteFlat_subgroup : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (B : Over (Sp R)) (_ : GrpObj B) (q : A ⟶ B) (π : B ⟶ A), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsFinite π.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
  first | exact @GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme | exact GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme | (intros; apply GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme <;> assumption)
