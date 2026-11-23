import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_pullback_basis : GlobalTheory.Published.BarsottiTateDieudonne.WittModule → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (h : (p : R) = 0) (G : PDivGroup p R), (∀ (n : ℕ) (b : Module.Basis (Fin n) R G.RigExt), LinearIndependent R (fun j => (frobProj h G).rig (b j)) ∧ Submodule.span R (Set.range fun j => (frobProj h G).rig (b j)) = ⊤) ∧ LinearMap.range (frobTwist h G).rigOfOmega = Submodule.span R ((frobProj h G).rig '' (LinearMap.range G.rigOfOmega : Set G.RigExt)) := by
  first | exact @GlobalTheory.PDivGroup.rigExt_frobTwist | exact GlobalTheory.PDivGroup.rigExt_frobTwist | (intros; apply GlobalTheory.PDivGroup.rigExt_frobTwist <;> assumption)
