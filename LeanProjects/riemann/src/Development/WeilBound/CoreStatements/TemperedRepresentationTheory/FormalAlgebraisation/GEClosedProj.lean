import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out

namespace PositivityTheory.FormalThickening

def GEClosed : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (P : Over (Spec (CommRingCat.of R))), IsSeparated P.hom → LocallyOfFiniteType P.hom →
      QuasiCompact P.hom →
    ∀ (C : ℕ → Scheme.{0}) (i : ∀ e, C e ⟶ (thickObj R I e P).left) (β : ∀ e, C e ⟶ C (e + 1)),
      (∀ e, IsClosedImmersion (i e)) →
      (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P)) →
      IsProper (i 0 ≫ (thickObj R I 0 P).hom) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ P.left) (b : ∀ e, C e ⟶ C'),
      IsClosedImmersion j ∧ IsProper (j ≫ P.hom) ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst P.hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e

def GEClosedProj : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ N : ℕ,
    let P : Over (Spec (CommRingCat.of R)) :=
      Over.mk (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)
    ∀ (C : ℕ → Scheme.{0}) (i : ∀ e, C e ⟶ (thickObj R I e P).left) (β : ∀ e, C e ⟶ C (e + 1)),
      (∀ e, IsClosedImmersion (i e)) →
      (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ P.left) (b : ∀ e, C e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst P.hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e

def IsoOfThick : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X), IsProper X.hom → IsProper p.left →
      (∀ e, IsIso ((Over.pullback (thick R I e)).map p).left) → IsIso p

end PositivityTheory.FormalThickening
