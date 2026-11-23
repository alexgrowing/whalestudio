import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsAddEquivOfSplitTorusIso

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LinearUnifCheck

section Torus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem torusEndOf_iff (h : X → X) (t : splitTorus S X ⟶ splitTorus S X) : TorusEndOf X h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusEndOf_unique {h : X → X} {t t' : splitTorus S X ⟶ splitTorus S X}
    (ht : TorusEndOf X h t) (ht' : TorusEndOf X h t') : t = t' := by
  refine (splitTorusPointsEquiv S X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusEndOf_iff _ _).1 ht,
    (torusEndOf_iff _ _).1 ht']

theorem torusEndOf_comp {h h' : X → X} {t t' : splitTorus S X ⟶ splitTorus S X}
    (ht : TorusEndOf X h t) (ht' : TorusEndOf X h' t') : TorusEndOf X (h ∘ h') (t ≫ t') :=
  (torusEndOf_iff _ _).2 fun χ => by
    rw [SplitTorusHom.appTop_comp, (torusEndOf_iff _ _).1 ht', (torusEndOf_iff _ _).1 ht]; rfl

end Torus

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {O : Type} [Ring O] [StarRing O] {D : DegData R I} [Module O D.toPre.X]
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O)

end GlobalTheory.LinearUnifCheck
