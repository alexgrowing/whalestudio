import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorsionLiftPairingInOrthogonalFrame
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_pairing_in_orthogonal_frame : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ) (n m s s₀ : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)), (∀ z : Qbar, ι (z : ℂ) = lam z) → S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → (∀ i, b i ∈ S.La) → IsIdem lam S.d m eps → 2 * n ≤ m → (s₀ * ∏ i, a i) ∣ s → let y' : Fin g → ℂ := fun i => beta S.d S.Hm ((s : ℂ) • liftY q n eps b y) (x i) / (a i : ℂ); (∀ i, Good ι S.d n s₀ (y' i)) ∧ ∀ (A : Fin r → ℤ_[q]) (A' : Fin g → ℤ_[q]), (∀ i, GlobalTheory.MomOne.zc (A' i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j))) → kap S.Hm (vecA n b A) ((s : ℂ) • liftY q n eps b y) ∈ Qbar ∧ ι (kap S.Hm (vecA n b A) ((s : ℂ) • liftY q n eps b y)) = ∏ i, ι (kap1 S.d 1 (y' i)) ^ (PadicInt.toZModPow n (A' i)).val := by
  first | exact @GlobalTheory.MomOne.kapFrame | exact GlobalTheory.MomOne.kapFrame | (intros; apply GlobalTheory.MomOne.kapFrame <;> assumption)
