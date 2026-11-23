import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsNatMulMemConeRingIntFin
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFrameChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHSMTransport
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace FrameChange

section Matrices

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem matAct_matAct (A A' : Matrix J J ℚ) (x : J → Ω) : matAct A (matAct A' x) = matAct (A * A') x := by
  funext i
  simp only [matAct, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem isInvMat_mul {A A' : Matrix J J ℚ} (hA : IsInvMat A) (hA' : IsInvMat A') : IsInvMat (A * A') := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨C', hC'⟩ := hA'
  refine ⟨C' * C, fun v => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC' (C.mulVec v)).1, (hC v).1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC (A'.mulVec v)).2, (hC' v).2]

open Classical in

def scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) : Matrix J J ℚ :=
  Matrix.diagonal fun i => if i ∈ Set.range e then 1 else (m : ℚ)

open Classical in

theorem matAct_scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) (y : J → Ω) :
    matAct (scaleMat e m) y = scaleOff e m y := by
  funext i
  simp only [matAct, scaleMat, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  rw [if_pos rfl]
  unfold scaleOff
  split_ifs <;> simp

open Classical in

theorem isInvMat_scaleMat {D : ℕ} (e : Fin (D + 1) → J) {m : ℕ} (hm : 0 < m) : IsInvMat (scaleMat e m) := by
  have hc : ∀ i, (if i ∈ Set.range e then 1 else (m : ℚ)) ≠ 0 := fun i => by
    split_ifs
    · exact one_ne_zero
    · exact_mod_cast hm.ne'
  refine ⟨Matrix.diagonal fun i => (if i ∈ Set.range e then 1 else (m : ℚ))⁻¹, fun v => ⟨?_, ?_⟩⟩
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, mul_inv_cancel₀ (hc i), one_mul]
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, inv_mul_cancel₀ (hc i), one_mul]

end Matrices

theorem proof (hN : RatNoetherFrame.Statement) (hT : HSMTransport.Statement) (hI : ResChiIndex.Statement) :
    FrameChange.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨B₀, e, hB₀, hfr⟩ := hN D Ω κ d.x d.arith
  obtain ⟨m, hm, hfr'⟩ := exists_scaleOff_isProjFrame (matAct B₀ d.x) e hfr
  have hB : IsInvMat (scaleMat e m * B₀) := isInvMat_mul (isInvMat_scaleMat e hm) hB₀
  obtain ⟨d', hx', hm', hG⟩ := hT D Ω κ d _ hB
  have hx'' : d'.x = scaleOff e m (matAct B₀ d.x) := by
    rw [hx', ← matAct_matAct, matAct_scaleMat]
  refine ⟨_, d', e, hB, hx', hm', by rw [hx'']; exact hfr', ?_⟩
  have h0 := hI D Ω κ d d' _ hB hx' hG
  have hz : (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) = fun _ => (0 : ℝ) :=
    funext fun n => by rw [h0 n, sub_self]
  rw [hz]
  exact isLittleO_zero _ _

end FrameChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
