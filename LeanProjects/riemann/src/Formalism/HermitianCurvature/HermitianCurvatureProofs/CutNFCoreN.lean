import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCoreNExt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFBddPtw
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTrNormKB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFOpOKMulGPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomVMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtwAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEPairAtDeriv

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section aux

variable {P : M.Par}

theorem nf_actA_fsum (a : MA.A P (MA.DQ P)) {κ : Type} (s : Finset κ) (g : κ → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (∑ k ∈ s, g k) = ∑ k ∈ s, MA.actA P a (g k) := by
  funext π
  rw [Finset.sum_apply]
  unfold MA.actA
  calc ∑ π', (a π π').1 ((∑ c ∈ s, g c) π') = ∑ π', ∑ c ∈ s, (a π π').1 (g c π') := by
        refine Finset.sum_congr rfl fun π' _ => ?_
        rw [Finset.sum_apply]
        exact map_sum (a π π').1 (fun c => g c π') s
    _ = ∑ c ∈ s, ∑ π', (a π π').1 (g c π') := Finset.sum_comm

theorem nf_norm_sum_sq {E : Type*} [SeminormedAddCommGroup E] {κ : Type*} (s : Finset κ) (a : κ → E) :
    ‖∑ k ∈ s, a k‖ ^ 2 ≤ s.card * ∑ k ∈ s, ‖a k‖ ^ 2 := by
  calc ‖∑ k ∈ s, a k‖ ^ 2 ≤ (∑ k ∈ s, ‖a k‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ s.card * ∑ k ∈ s, ‖a k‖ ^ 2 := sq_sum_le_card_mul_sum_sq

theorem nf_pow_le (G : ℝ) (hG : 0 ≤ G) {a N : ℕ} (ha : a ≤ N) : G ^ a ≤ 1 + G ^ (2 * N) := by
  rcases le_total G 1 with h | h
  · have h1 : G ^ a ≤ 1 := pow_le_one₀ hG h
    have h2 : 0 ≤ G ^ (2 * N) := pow_nonneg hG _
    linarith
  · have h1 : G ^ a ≤ G ^ (2 * N) := pow_le_pow_right₀ h (by omega)
    linarith

end aux

end

end Formalism.FourierDecayAlt.P.CutBP
