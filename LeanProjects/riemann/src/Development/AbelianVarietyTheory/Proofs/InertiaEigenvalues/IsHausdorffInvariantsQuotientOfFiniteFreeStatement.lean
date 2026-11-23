import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHausdorffInvariantsQuotientOfFiniteFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHausdorff_invariants_quotient_of_finiteFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D → IsHausdorff (Ideal.span {(l : O)}) D.Z := by
  first | exact @GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree | exact GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree | (intros; apply GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree <;> assumption)
