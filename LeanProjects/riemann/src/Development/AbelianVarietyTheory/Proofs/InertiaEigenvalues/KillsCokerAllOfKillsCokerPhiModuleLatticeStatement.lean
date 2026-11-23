import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLattice
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ r : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ r) D₁.L D₂.L → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsAll F (l ^ r) := by
  first | exact @GlobalTheory.CokerLift.killsAll_of_killsCoker_L | exact GlobalTheory.CokerLift.killsAll_of_killsCoker_L | (intros; apply GlobalTheory.CokerLift.killsAll_of_killsCoker_L <;> assumption)
