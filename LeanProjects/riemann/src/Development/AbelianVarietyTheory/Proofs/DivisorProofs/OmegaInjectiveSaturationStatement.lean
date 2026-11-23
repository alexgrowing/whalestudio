import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaInjectiveSaturation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_injective_saturation : GlobalTheory.Published.BarsottiTateDieudonne.WittModule → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (h : (p : R) = 0) (G H : PDivGroup p R) (f : G ⟶ H), Function.Injective (omegaMap G H f) → (∀ x : G.VecExt, ∃ r : R, r ≠ 0 ∧ r • x ∈ LinearMap.range (vecExtMap f)) → (∀ (r : R) (w : G.omega), r ≠ 0 → r • w ∈ LinearMap.range (omegaMap G H f) → w ∈ LinearMap.range (omegaMap G H f)) ∧ Function.Surjective (vecExtMap f) := by
  first | exact @GlobalTheory.PDivGroup.saturated_omegaMap_and_surjective_vecExtMap | exact GlobalTheory.PDivGroup.saturated_omegaMap_and_surjective_vecExtMap | (intros; apply GlobalTheory.PDivGroup.saturated_omegaMap_and_surjective_vecExtMap <;> assumption)
