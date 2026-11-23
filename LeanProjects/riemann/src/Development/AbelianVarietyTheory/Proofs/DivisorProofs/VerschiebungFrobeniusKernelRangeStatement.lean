import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerschiebungFrobeniusKernelRange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.verschiebung_frobenius_kernel_range : GlobalTheory.Published.BarsottiTateDieudonne.WittModule → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (h : (p : R) = 0) (G : PDivGroup p R), LinearMap.range (rigExtMap (verschiebung h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧ LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧ LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) ∧ LinearMap.range (rigExtMap (relFrob h G)) = Submodule.span R (Set.range (absFrob h G).rig) := by
  first | exact @GlobalTheory.PDivGroup.exact_frobenius_verschiebung_of_isDiscreteValuationRing | exact GlobalTheory.PDivGroup.exact_frobenius_verschiebung_of_isDiscreteValuationRing | (intros; apply GlobalTheory.PDivGroup.exact_frobenius_verschiebung_of_isDiscreteValuationRing <;> assumption)
