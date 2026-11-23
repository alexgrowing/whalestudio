import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRingEmbeddingProperties
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_embedding_properties : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ K : FinExt l, ∃ Ψ : BK K →+* P.R.BdR,
      (∀ c : ↥K.1, Ψ (inK K c) = algebraMap ↥K.1 P.R.BdR c) ∧
      (∀ (g : ↥(GK K)) (b : BK K), (P.PD K).actdR g (Ψ b) = Ψ (galB g b)) ∧
      (∀ b, Ψ b ∈ (P.PD K).Fil 0) ∧
      (∀ x : AK K, thetaK K x = 0 → Ψ (toB K (ofA K x)) ∈ (P.PD K).Fil 1) ∧
      (∀ x : AK K, thetaK K x = 0 → x ∉ RingHom.ker (thetaK K) ^ 2 → Ψ (toB K (ofA K x)) ∉ (P.PD K).Fil 2) := by
  first | exact @GlobalTheory.CrisToDR.exists_map | exact GlobalTheory.CrisToDR.exists_map | (intros; apply GlobalTheory.CrisToDR.exists_map <;> assumption)
