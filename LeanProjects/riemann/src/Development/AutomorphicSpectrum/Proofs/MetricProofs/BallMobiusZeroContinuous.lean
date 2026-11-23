import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

open Matrix GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem IsSgU.det_toBlocks₁₁_ne_zero {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) :
    u.toBlocks₁₁.det ≠ 0 := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, u = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  rw [toBlocks_fromBlocks₁₁]
  unfold IsSgU sgI at hu
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at hu
  have h := (fromBlocks_inj.1 hu).1
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg] at h
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h1 : -(Cᴴ *ᵥ (C *ᵥ v)) = v := by
    have h2 := congrArg (fun M => M *ᵥ v) h
    simp only [Matrix.add_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hAv,
      Matrix.mulVec_zero, zero_add] at h2
    exact h2
  have h3 : star v ⬝ᵥ v = -(star (C *ᵥ v) ⬝ᵥ (C *ᵥ v)) := by
    calc star v ⬝ᵥ v = star v ⬝ᵥ (-(Cᴴ *ᵥ (C *ᵥ v))) := by rw [h1]
      _ = -(star (C *ᵥ v) ⬝ᵥ (C *ᵥ v)) := by
        rw [dotProduct_neg, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have h4 : 0 ≤ star v ⬝ᵥ v := dotProduct_star_self_nonneg v
  have h5 : 0 ≤ star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) := dotProduct_star_self_nonneg _
  have h6 : star v ⬝ᵥ v = 0 := le_antisymm (by rw [h3]; exact neg_nonpos.2 h5) h4
  exact hv (dotProduct_star_self_eq_zero.1 h6)

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) : moebW u 0 = u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ := by
  simp [moebW]

theorem continuous_matrix_inv {X m : Type} [TopologicalSpace X] [Fintype m] [DecidableEq m]
    {A : X → Matrix m m ℂ} (hA : Continuous A) (hd : ∀ x, (A x).det ≠ 0) :
    Continuous fun x => (A x)⁻¹ := by
  have h : (fun x => (A x)⁻¹) = fun x => ((A x).det)⁻¹ • (A x).adjugate := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hA.matrix_det.inv₀ hd).smul hA.matrix_adjugate

theorem continuous_moebBall_zero (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (X : Type) [TopologicalSpace X] (f : X → Ψ → Matrix (Sg j j') (Sg j j') ℂ)
    (hc : ∀ τ, Continuous fun x => f x τ) (hu : ∀ x τ, IsSgU (f x τ)) :
    Continuous fun x => moebBall q (f x) 0 := by
  have hb : ∀ τ, (ballMat q 0 τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  refine continuous_pi fun k => ?_
  simp only [moebBall, ballPt, hb, moebW_zero]
  set τ := (q.symm k).1
  have h11 : Continuous fun x => (f x τ).toBlocks₁₁ :=
    continuous_matrix fun a b => (hc τ).matrix_elem _ _
  have h21 : Continuous fun x => (f x τ).toBlocks₂₁ :=
    continuous_matrix fun a b => (hc τ).matrix_elem _ _
  have hm := h21.matrix_mul (continuous_matrix_inv h11 fun x => (hu x τ).det_toBlocks₁₁_ne_zero)
  exact hm.matrix_elem _ _

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
