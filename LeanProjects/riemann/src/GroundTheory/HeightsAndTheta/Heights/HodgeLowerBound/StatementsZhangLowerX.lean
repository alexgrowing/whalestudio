import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

def ZhangLowerX.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (n : ℕ)
    (A : HermLine ι) (e : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (n + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → e ≤ IndefiniteRowSideFullHecke.HeightsSet.height (II K ι) A W) →
    ((n + 1 : ℕ) : ℝ) * e * geomDeg P A n ≤ II K ι P (n + 1) (fun _ => A)

theorem ZhangLowerX.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.GlobalTheory (Fin 2)) HilbertSamuel.ProjLine.y) (1 + 1) ∧
      ⊥ ≤ mCoordIdeal (ι := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.GlobalTheory (Fin 2)) HilbertSamuel.ProjLine.y ∧
      IsSemipositiveRel ⊥ (mCoordIdeal (ι := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.GlobalTheory (Fin 2)) HilbertSamuel.ProjLine.y)
        HilbertSamuel.ProjLine.fsLine1 ∧
      NefOnFibres (mCoordIdeal (ι := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.GlobalTheory (Fin 2)) HilbertSamuel.ProjLine.y)
        HilbertSamuel.ProjLine.fsLine1.a ∧
      IsConjInvariantH HilbertSamuel.ProjLine.fsLine1 :=
  HilbertSamuel.G5.hyps_inhabited

end GroundTheory.Heights₂.Heights.LowerBoundFree
