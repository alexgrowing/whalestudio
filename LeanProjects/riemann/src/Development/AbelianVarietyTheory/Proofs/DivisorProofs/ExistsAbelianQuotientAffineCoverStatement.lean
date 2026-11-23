import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianQuotientAffineCover
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianQuotient_affineCover : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∀ j : S.affineCover.I₀,
    ∃ (B : Over (S.affineCover.X j)) (_ : GrpObj B) (q : (Over.pullback (S.affineCover.f j)).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A) ≫
          (Over.pullback (S.affineCover.f j)).map i) *
          snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A))
        (snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A)) q q := by
  first | (exact @GlobalTheory.AbQuotientLocal.exists_local_quotient) | (exact GlobalTheory.AbQuotientLocal.exists_local_quotient) | (intros; apply GlobalTheory.AbQuotientLocal.exists_local_quotient  <;> assumption)
