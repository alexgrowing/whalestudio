import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V), IsAdicComplete (maximalIdeal V) V → Function.Injective φ → I.map φ ≤ maximalIdeal V → ∃ (D' : DegData V (maximalIdeal V)) (hD : IsPullDeg φ D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (U' : Unif (maximalIdeal V) D' A' ((Over.pullback (specOf φ)).obj G)), IsSemiAbelian ((Over.pullback (specOf φ)).obj G) ∧ IsPullUnif φ hD (Iso.refl _) U U' ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing V) F (algebraMap V _ (φ r))) → (∀ g, ∃! g', IsPullGtF φ hD F g g') ∧ (∀ g', ∃! g, IsPullGtF φ hD F g g') ∧ (∀ g g' y, IsPullGtF φ hD F g g' → (GtPtF.IsIota (hD.xe y) g ↔ GtPtF.IsIota y g')) ∧ ∀ k g g' h h', IsPullGtF φ hD F g g' → IsPullGtF φ hD F h h' → (GtPtF.IsNsmul k g h ↔ GtPtF.IsNsmul k g' h')) ∧ ∀ E : EndU U.toUnifPre, ∃ E' : EndU U'.toUnifPre, E'.aG = (Over.pullback (specOf φ)).map E.aG ∧ (∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing V) F (algebraMap V _ (φ r))) → ∀ g₁ g₂ g₁' g₂', IsPullGtF φ hD F g₁ g₁' → IsPullGtF φ hD F g₂ g₂' → (E.Act g₁ g₂ ↔ E'.Act g₁' g₂') := by
  first | exact @GlobalTheory.UT.EndBaseChange.main | exact GlobalTheory.UT.EndBaseChange.main | (intros; apply GlobalTheory.UT.EndBaseChange.main <;> assumption)
