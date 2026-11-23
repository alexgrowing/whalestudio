import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_of_generic_principal_special_ample : Out.Laws → Out.Laws2 → ∀ (h k : ℕ), Odd k → 3 ≤ k → ∀ (B : Type) [CommRing B] (ζ : B) (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsLocalRing O] [Algebra O C], IsUnitBall O C → ∀ p : ℕ, p.Prime → ‖(p : C)‖ < 1 → ∀ (β : B →+* O) (c : SiegPre h k ζ (spMap β)), (∃ c' : SiegPre h k ζ (spMap (algebraMap O C) ≫ spMap β), SiegPB c' c (spMap (algebraMap O C)) ∧ c'.Principal) → Out.RelAmple (Over.mk (pullback.snd c.A.hom (spMap (IsLocalRing.residue O)))) (c.diag.pull (pullback.fst c.A.hom (spMap (IsLocalRing.residue O)))) → c.Principal := by
  first | exact @GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special | exact GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special | (intros; apply GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special <;> assumption)
