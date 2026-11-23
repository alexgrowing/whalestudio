import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjExtendPrincipalCongruenceCongOneModQ
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (c j D : ℕ) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : GLint E n P), κ ∈ GlobalTheory.TopStep.prinCong n P D → j + 1 ≤ D → (∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ ((qOf P : E) ^ j) • h x ∈ stdAt E (n + c) P) → ∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • ((h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x) ∈ stdAt E (n + c) P := by
  first | exact @GlobalTheory.QCong.conj_extE_cong | exact GlobalTheory.QCong.conj_extE_cong | (intros; apply GlobalTheory.QCong.conj_extE_cong <;> assumption)
