import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LineBase

theorem u_eq {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ha : a = a') (hb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    D.u a b h = D.u a' b' h' := by
  subst ha hb
  rfl

noncomputable def pull {X' X : Scheme.{0}} (g : X' ⟶ X) (D : LineData X) : LineData X' where
  Y := pullback D.f g
  f := pullback.snd D.f g
  sm := by
    exact MorphismProperty.pullback_snd (P := @Smooth) D.f g D.sm
  surj := by
    exact MorphismProperty.pullback_snd (P := @Surjective) D.f g D.surj
  u := fun {V} a b h => D.u (a ≫ pullback.fst D.f g) (b ≫ pullback.fst D.f g) (by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, h])
  nat := fun {V' V} k a b h => by
    rw [← D.nat k (a ≫ pullback.fst D.f g) (b ≫ pullback.fst D.f g)]
    exact u_eq D (Category.assoc _ _ _) (Category.assoc _ _ _) _ _
  coc := fun {V} a b c h h' => D.coc _ _ _ _ _

theorem lineBC : CrystallineSemistableComparison.E.LineBC := by
  intro X' X g D
  refine ⟨pull g D, pullback.fst D.f g, pullback.condition, ?_, ?_⟩
  · intro V a x h
    exact ⟨pullback.lift a x h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  · intro V a b h h'
    rfl

end GlobalTheory.CompanionTheory.LineBase
