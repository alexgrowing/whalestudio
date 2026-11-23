import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBoundRingActionPullback
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_bound_ringAction_pullback : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (c : ℕ), H.IsLB ∧ GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ 1 ≤ c ∧ ∀ (n : Fin d → ℤ) (K : ℕ), 1 ≤ K → (∀ i, (n i).natAbs ≤ K) → ∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left))) (j : (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left)).ι), σ.f j ≠ 0 := by
  first | exact @GlobalTheory.OEndDegree.exists_effective_bound | exact GlobalTheory.OEndDegree.exists_effective_bound | (intros; apply GlobalTheory.OEndDegree.exists_effective_bound <;> assumption)
