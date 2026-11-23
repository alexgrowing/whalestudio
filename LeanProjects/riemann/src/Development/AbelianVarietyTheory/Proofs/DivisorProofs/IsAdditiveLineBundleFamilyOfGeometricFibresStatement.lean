import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibres
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left], IsAbelianScheme A → ∀ (N : LB (A ⊗ T).left) (hN : N.IsLB), Triv (ev N (1 : T ⟶ A) (𝟙 T)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T), IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) → IsAdditive N := by
  first | exact @GlobalTheory.AddFib.isAdditive_of_geomFibres | exact GlobalTheory.AddFib.isAdditive_of_geomFibres | (intros; apply GlobalTheory.AddFib.isAdditive_of_geomFibres <;> assumption)
