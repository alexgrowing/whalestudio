import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairOfLambdaBundleIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (M : LB A.left), P.IsLB → M.IsLB → LBIso P (cubeLB A ![fst A A, snd A A] M) → ∀ (T : Over (Sp ℂ)) (a b : T ⟶ A), LBIso (P.pull (lift a b).left) (cubeLB A ![a, b] M) := by
  first | exact @GlobalTheory.LamPull.lbIso_pull_lift | exact GlobalTheory.LamPull.lbIso_pull_lift | (intros; apply GlobalTheory.LamPull.lbIso_pull_lift <;> assumption)
