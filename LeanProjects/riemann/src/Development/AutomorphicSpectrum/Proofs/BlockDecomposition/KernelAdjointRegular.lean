import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem continuousOn_inv_GLs {n : ℕ} : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have h : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((continuous_id.matrix_det).continuousOn.inv₀ (fun y hy => hy)).smul
    (continuous_id.matrix_adjugate).continuousOn

theorem unitary_matrix_inv {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (k.1 : Mat n)⁻¹ = (k⁻¹).1 := by
  apply Matrix.inv_eq_left_inv
  have := congrArg Subtype.val (inv_mul_cancel k)
  simpa using this

theorem adjoint_rho_inv {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  let f : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k : E.V →L[ℂ] E.V).toLinearMap, E.iso k⟩
  have h1 : E.ρ k (E.ρ k⁻¹ y) = y := by
    have : E.ρ k * E.ρ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun T : E.V →L[ℂ] E.V => T y) this
  have h2 := f.inner_map_map x (E.ρ k⁻¹ y)
  have h3 : f (E.ρ k⁻¹ y) = y := h1
  rw [h3] at h2
  exact h2

theorem adjoint_kernel_reg : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  intro hL n E k hk heq
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨hc, R, hR⟩ := hk
  refine ⟨⟨?_, R, ?_⟩, ?_⟩
  · have hinv : ContinuousOn (fun y : Mat n => k y⁻¹) (GLs n) :=
      hc.comp continuousOn_inv_GLs (fun y hy => inv_mem_GLs hy)
    exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E.V) (F := E.V)).continuous.comp_continuousOn hinv
  · intro y hy hlt
    have h1 : lg y⁻¹ = lg y := (hL n).2.1 y hy
    have h2 : k y⁻¹ = 0 := hR _ (inv_mem_GLs hy) (by rw [h1]; exact hlt)
    simp [h2]
  · intro y hy k₁ k₂
    have h1 : ((k₁.1 : Mat n) * y * k₂.1)⁻¹ = (k₂⁻¹).1 * y⁻¹ * (k₁⁻¹).1 := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, unitary_matrix_inv, unitary_matrix_inv, mul_assoc]
    rw [h1, heq _ (inv_mem_GLs hy)]
    have h2 : ContinuousLinearMap.adjoint (E.ρ k₂⁻¹ * k y⁻¹ * E.ρ k₁⁻¹)
        = ContinuousLinearMap.adjoint (E.ρ k₁⁻¹) * ContinuousLinearMap.adjoint (k y⁻¹)
          * ContinuousLinearMap.adjoint (E.ρ k₂⁻¹) := by
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
      rfl
    rw [h2, adjoint_rho_inv, adjoint_rho_inv]

end GlobalTheory.CompanionTheory.WaveMult
