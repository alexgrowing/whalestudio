import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorExtensionSurjectiveField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_extension_surjective_field : GlobalTheory.Published.BarsottiTateDieudonne.WittModule → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G H : PDivGroup p K) (f : G ⟶ H), Function.Surjective (f.app 1) → Function.Bijective (omegaMap G H f) → Function.Surjective (vecExtMap f) := by
  first | exact @GlobalTheory.PDivGroup.vecExtMap_surjective_of_omegaMap_bijective | exact GlobalTheory.PDivGroup.vecExtMap_surjective_of_omegaMap_bijective | (intros; apply GlobalTheory.PDivGroup.vecExtMap_surjective_of_omegaMap_bijective <;> assumption)
