import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem piW_mat_inv_mulVec_incV_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) (x : Fin n → E), x ≠ 0 →
    (fun k => piW B.τ₁ ((mat g⁻¹ *ᵥ incV F x) k)) ≠ 0 := by
  intro F E _ _ _ _ _ σ B n J g x hx h
  apply hx
  set φ := piW B.τ₁ with hφ
  have hinc : (fun k => φ (incV F x k)) = fun k => B.τ₁ (x k) := by
    funext k
    exact GlobalTheory.HTensSplitPair.piW_inclR_eq B.τ₁ (x k)
  have hmv : (fun k => φ ((mat g⁻¹ *ᵥ incV F x) k)) = (mat g⁻¹).map φ *ᵥ (fun k => B.τ₁ (x k)) := by
    funext k
    rw [RingHom.map_mulVec, ← hinc]
    rfl
  have hone : mat g * mat g⁻¹ = 1 := by
    unfold mat
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  have hy : (fun k => B.τ₁ (x k)) = 0 := by
    have := congrArg (fun v => (mat g).map φ *ᵥ v) (hmv.symm.trans h)
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hone, Matrix.mulVec_zero] at this
    rw [Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec] at this
    exact this
  funext k
  have := congrFun hy k
  simpa using (map_eq_zero_iff B.τ₁ B.τ₁.toRingHom.injective).1 this

end GlobalTheory.ThKTorus
