import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSurjectiveCoverFromOpens
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_surjective_cover_from_opens : ∀ (X Z : Scheme.{0}) (i : X ⟶ Z) (T : Type) [Finite T] (M : T → Scheme.{0}) (U : T → Z.Opens) (g : ∀ t, M t ⟶ (U t).toScheme), (∀ t, IsFinite (g t)) → (∀ t, Set.range i ⊆ (U t : Set Z)) → (∀ x : X, ∃ (t : T) (w : M t), (g t ≫ (U t).ι) w ⤳ i x) → ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (yM : Sp K ⟶ M t), yM ≫ g t ≫ (U t).ι = y' ≫ q ≫ i := by
  first | exact @GlobalTheory.FinCover.exists_finite_surjective_cover | exact GlobalTheory.FinCover.exists_finite_surjective_cover | (intros; apply GlobalTheory.FinCover.exists_finite_surjective_cover <;> assumption)
