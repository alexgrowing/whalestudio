import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemStandardThetaLatticeIffAdelicIdeal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.PullMulRight

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car}

def phiU {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  phiL (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (Matrix.mem_unitaryGroup_iff'.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ.2)
    (Matrix.mem_unitaryGroup_iff'.mp γ'.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)

def cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix.unitaryGroup (Fin n) D.host.E :=
  ⟨(star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ) = (γ : Matrix (Fin n) (Fin n) D.host.E)ᵀ := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    rw [h, ← Matrix.transpose_mul, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.transpose_one]⟩

private theorem phiU_apply {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) :
    phiU γ γ' z τ = gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (z τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ := rfl

private theorem rowE_apply' {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (i : Fin N') (τ : D.what₂.Tau) (a : Fin 1) (j : Fin N) :
    rowE D N N' z i τ a j = z τ i j := rfl

private theorem colE_apply' {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (j : Fin N) (τ : D.what₂.Tau) (a : Fin 1) (i : Fin N') :
    colE D N N' z j τ a i = z τ i j := rfl

theorem map_row {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (x : TaylorLogMetric.VC D N N') (i : Fin N') :
    rowE D N N' (phiU γ 1 x) i = phiU γ 1 (rowE D N N' x i) := by
  funext τ a j
  rw [rowE_apply', phiU_apply, phiU_apply]
  simp [gM, Matrix.mul_apply, Matrix.one_apply, rowE_apply', Fin.fin_one_eq_zero a]

theorem map_col {N N' : ℕ} (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') (j : Fin N) :
    colE D N N' (phiU 1 γ' x) j = phiU (cjU γ') 1 (colE D N N' x j) := by
  funext τ a i
  rw [colE_apply', phiU_apply, phiU_apply]
  simp [gM, cjU, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, colE_apply',
    Fin.fin_one_eq_zero a, mul_comm, embT_star']

theorem det_gM {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : (gM M τ).det = TaylorLogMetric.embT D τ M.det :=
  ((TaylorLogMetric.embT D τ).map_det M).symm

theorem det_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) :
    ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).det =
      star (γ : Matrix (Fin n) (Fin n) D.host.E).det := by
  simp [cjU, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]

theorem ne_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0) :
    (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  intro h
  apply hγ
  have e : (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) =
      (star (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)))ᵀ := by
    simp [cjU, Matrix.transpose_sub, star_sub]
  rw [e, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h
  simpa using h

theorem det_row {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) :
    LinearMap.det ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) := by
  have h1 : ∀ τ : D.what₂.Tau,
      gM (((1 : Matrix.unitaryGroup (Fin 1) D.host.E)) : Matrix (Fin 1) (Fin 1) D.host.E) τ = 1 := by
    intro τ
    simp [gM]
  have key : ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      LinearMap.pi (fun τ : D.what₂.Tau =>
        (LinearMap.pi (fun a : Fin 1 =>
          (Matrix.toLin' ((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ) ∘ₗ LinearMap.proj a))
          ∘ₗ LinearMap.proj τ) := by
    apply LinearMap.ext
    intro z
    funext τ a j
    rw [LinearEquiv.coe_coe, phiU_apply, h1, Matrix.one_mul]
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
  rw [key, LinearMap.det_pi]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [LinearMap.det_pi, Fin.prod_univ_one, LinearMap.det_toLin', Matrix.det_transpose,
    Matrix.det_conjTranspose, det_gM, embT_star']

theorem finrank_row (N : ℕ) : Module.finrank ℂ (TaylorLogMetric.VC D N 1) = Fintype.card D.what₂.Tau * N := by
  simp [Module.finrank_pi_fintype]

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
