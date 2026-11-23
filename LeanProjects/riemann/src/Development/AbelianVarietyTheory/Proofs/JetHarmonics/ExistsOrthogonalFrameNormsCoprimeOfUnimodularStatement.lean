import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodular
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_frame_norms_coprime_of_unimodular : ∀ (q g : ℕ) (S : Setup g), q.Prime → S.Ok → ¬ q ∣ S.d → ∃ (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), (∀ i, x i ∈ S.La) ∧ (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) ∧ ∀ i, 0 < a i ∧ Nat.Coprime (a i) q := by
  first | exact @GlobalTheory.MomOne.exists_orthFrame | exact GlobalTheory.MomOne.exists_orthFrame | (intros; apply GlobalTheory.MomOne.exists_orthFrame <;> assumption)
