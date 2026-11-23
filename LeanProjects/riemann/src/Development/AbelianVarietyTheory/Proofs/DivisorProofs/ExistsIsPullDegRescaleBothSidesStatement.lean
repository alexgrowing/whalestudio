import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegRescaleBothSides
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_rescale_both_sides : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {Q : DegPre R} {Q' : DegPre V} (hD : IsPullDeg θ Q Q') (g : Q.X → (FractionRing R)ˣ) (g' : Q'.X → (FractionRing V)ˣ), Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) → (∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧ (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a)) → ∃ h : IsPullDeg θ (GlobalTheory.PolDeg.rescale Q g) (GlobalTheory.PolDeg.rescale Q' g'), h.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) = hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ∧ ∀ y, h.xe y = hD.xe y := by
  first | exact @GlobalTheory.RescaleBoth.exists_isPullDeg_rescale | exact GlobalTheory.RescaleBoth.exists_isPullDeg_rescale | (intros; apply GlobalTheory.RescaleBoth.exists_isPullDeg_rescale <;> assumption)
