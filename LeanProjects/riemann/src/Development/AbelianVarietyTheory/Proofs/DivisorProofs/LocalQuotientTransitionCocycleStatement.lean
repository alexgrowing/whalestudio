import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalQuotientTransitionCocycle
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_quotient_transition_cocycle : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) →
    (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) →
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    ∀ (j k l : 𝒰.I₀) (T : Scheme.{0}) (x : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k))
      (y : T ⟶ pullback ((B k).hom ≫ 𝒰.f k) (𝒰.f l)) (z : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f l)),
      x ≫ b j k = y ≫ pullback.fst _ _ → x ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ → y ≫ b k l = z ≫ b j l := by
  first | (exact @GlobalTheory.cocycle_local_quotient_transition) | (exact GlobalTheory.cocycle_local_quotient_transition) | (intros; apply GlobalTheory.cocycle_local_quotient_transition  <;> assumption)
