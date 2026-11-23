import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem rdV_leftCov {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g))
    {μ : Q.Mx k r} (hμ : μ ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z X) :
    RdV (μ⁻¹ * X * μ) F μ = (P.QrD.dOp π X).comp (F μ) := by
  have hU : μᴴ * Hpk k r * μ = Hpk k r := hμ.1.1
  have hdet : IsUnit μ.det := by
    apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * μᴴ * Hpk k r)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc μᴴ, hU, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hμu : IsUnit μ := (Matrix.isUnit_iff_isUnit_det μ).mpr hdet
  have key : ∀ t : ℝ, F (μ * NormedSpace.exp ((t : ℂ) • (μ⁻¹ * X * μ))) =
      (π (NormedSpace.exp ((t : ℂ) • X))).comp (F μ) := by
    intro t
    rw [show (t : ℂ) • (μ⁻¹ * X * μ) = μ⁻¹ * ((t : ℂ) • X) * μ by rw [Matrix.mul_smul, Matrix.smul_mul],
      Matrix.exp_conj' μ _ hμu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    exact hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) μ hμ
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (F μ)).restrictScalars ℝ
  have hL : ∀ A, L A = A.comp (F μ) := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

theorem left_covariance_holds : LeftCov := by
  intro k r z Wp Wq _ _ _ _ _ _ π hπ hc _ D F _ _ _ hF μ hμ B hB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.1.1
  · rw [P.LeftDerivativeCurves.hpart2_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.2.1
  · unfold Rc P.QrD.ecOp
    rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1, P.LeftDerivativeCurves.hpart2_conj hμ.1.1, rdV_leftCov hπ hc hF hμ hB.1,
      rdV_leftCov hπ hc hF hμ hB.2]
    ext v
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
