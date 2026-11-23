import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.DifferentiableAdjugate
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.EpowCongr

noncomputable section

open Matrix
open scoped Kronecker

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {κ μ : Type} [Fintype κ] [Fintype μ]

def kronLin (κ μ : Type) [Fintype κ] [Fintype μ] :
    Matrix κ κ ℂ →ₗ[ℝ] Matrix μ μ ℂ →ₗ[ℝ] Matrix (κ × μ) (κ × μ) ℂ :=
  LinearMap.mk₂ ℝ (fun A B => A ⊗ₖ B) (fun A A' B => Matrix.add_kronecker A A' B)
    (fun c A B => by rw [Matrix.smul_kronecker]) (fun A B B' => Matrix.kronecker_add A B B')
    (fun c A B => by rw [Matrix.kronecker_smul])

def kronC (κ μ : Type) [Fintype κ] [Fintype μ] :
    Matrix κ κ ℂ →L[ℝ] Matrix μ μ ℂ →L[ℝ] Matrix (κ × μ) (κ × μ) ℂ :=
  LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (Matrix μ μ ℂ →ₗ[ℝ] Matrix (κ × μ) (κ × μ) ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ kronLin κ μ)

variable {n : ℕ}

theorem differentiable_Mt : Differentiable ℝ (Mt (n := n)) := by
  intro y
  refine dMat fun p q => ?_
  have hM : DifferentiableAt ℝ (fun z : Mat n => z * hbM q * zᴴ * hbM p) y :=
    dMul (dMul (dMul differentiableAt_id (dConst _)) (dConjT differentiableAt_id)) (dConst _)
  have ht : DifferentiableAt ℝ (fun z : Mat n => (z * hbM q * zᴴ * hbM p).trace) y := by
    simp only [Matrix.trace, Matrix.diag]
    exact DifferentiableAt.fun_sum fun i _ => dEntry hM i i
  exact (Complex.ofRealCLM.comp Complex.reCLM).differentiableAt.comp y ht

end PositivityTheory.RgBcC.Cxf

namespace PositivityTheory.RgBcC

open Cxf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fr0Der_of (hG : GamDer) (hGm : GamMul) (hM : MtLaws) (hR : RmLaws) : MatrixFrechetDerivativeAtZero := by
  intro n lam
  have hdet1 : (1 : PositivityTheory.RgTw.Mat n).det ≠ 0 := by simp
  have hopen : IsOpen (GLs n) :=
    isOpen_ne_fun (differentiable_det (ι := Fin n)).continuous continuous_const
  have hRm : ∀ y : PositivityTheory.RgTw.Mat n, y.det ≠ 0 → DifferentiableAt ℝ (Rm lam) y := fun y hy =>
    ((hR n lam).2.2.contDiffAt (hopen.mem_nhds (show y ∈ GLs n from hy))).differentiableAt (by simp)
  have hdetR : (Rm lam (1 : PositivityTheory.RgTw.Mat n)).det ≠ 0 := by rw [(hR n lam).1]; simp
  have hgam : ∀ B : Matrix (Md n) (Md n) ℂ, DifferentiableAt ℝ (gamM (n := n)) B := fun B =>
    (((hG n).1.differentiable (by simp)) B).restrictScalars ℝ
  have hFd : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => gamM (Mt x⁻¹)ᵀ) 1 :=
    (hgam _).comp (1 : PositivityTheory.RgTw.Mat n)
      (dT ((differentiable_Mt _).comp (1 : PositivityTheory.RgTw.Mat n) (differentiableAt_inv 1 hdet1)))
  have hA : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => (Rm lam x)⁻¹ᵀ) 1 :=
    dT ((differentiableAt_inv _ hdetR).comp (1 : PositivityTheory.RgTw.Mat n) (hRm 1 hdet1))
  have hB : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => (Rm lam xᴴ)ᵀ) 1 :=
    dT ((hRm _ (by simp)).comp (1 : PositivityTheory.RgTw.Mat n) (dConjT differentiableAt_id))
  have hGd : DifferentiableAt ℝ (rhoW lam) 1 := by
    have h := ((kronC _ _).hasFDerivAt_of_bilinear hA.hasFDerivAt hB.hasFDerivAt).differentiableAt
    exact h
  have key : fr0 lam = fun x => kronC _ _ (gamM (Mt x⁻¹)ᵀ) (rhoW lam x) := rfl
  have hF1 : gamM (Mt (1 : PositivityTheory.RgTw.Mat n)⁻¹)ᵀ = 1 := by
    rw [inv_one, (hM n).1, transpose_one, (hGm n).1]
  have hG1 : rhoW lam (1 : PositivityTheory.RgTw.Mat n) = 1 := by
    simp only [rhoW, conjTranspose_one, (hR n lam).1, inv_one, transpose_one]
    exact Matrix.one_kronecker_one
  refine ⟨?_, fun X _ => ?_⟩
  · rw [key]
    exact ((kronC _ _).hasFDerivAt_of_bilinear hFd.hasFDerivAt hGd.hasFDerivAt).differentiableAt
  · have h := congrArg (fun L => L X) ((kronC _ _).fderiv_of_bilinear hFd hGd)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, hF1, hG1] at h
    rw [key]
    refine h.trans ?_
    rw [add_comm]
    rfl

end PositivityTheory.RgBcC
