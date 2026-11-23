import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectExistsCharZeroLift
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_object_exists_charZero_lift : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (βV : cycAway n →+* V) (π : V →+* K) (cV : SiegPre g n (zetaAway n) (spMap βV)), Function.Injective βV ∧ π.comp βV = β ∧ cV.Principal ∧ SiegPB c cV (spMap π) := by
  first | exact @GlobalTheory.SiegLift0.exists_lift_domain | exact GlobalTheory.SiegLift0.exists_lift_domain | (intros; apply GlobalTheory.SiegLift0.exists_lift_domain <;> assumption)
