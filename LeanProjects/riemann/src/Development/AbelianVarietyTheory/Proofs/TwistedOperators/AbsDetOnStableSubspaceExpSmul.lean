import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
open Matrix

namespace GlobalTheory.FlagMeas

theorem detOn_exp_smul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)),
    (∀ y ∈ V, A *ᵥ y ∈ V) → ∃ c : ℝ, ∀ t : ℝ,
      GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) := by
  intro n A V hA
  have hA' : ∀ y ∈ V, Matrix.toLin' A y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hA y hy
  set f : V →ₗ[ℂ] V := (Matrix.toLin' A).restrict hA' with hf
  set b := Module.finBasis ℂ V with hb
  set B := LinearMap.toMatrixAlgEquiv b f with hB
  refine ⟨(B.trace).re, fun t => ?_⟩
  have hts : t • A = (t : ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [hts]
  set s : ℂ := (t : ℂ) with hs
  have hpowA : ∀ (k : ℕ) (v : V), (s • A) ^ k *ᵥ (v : Fin n → ℂ) = (((s • f) ^ k) v : Fin n → ℂ) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih, Module.End.mul_apply]
      simp [hf, LinearMap.restrict_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
  have hpowB : ∀ k : ℕ, Matrix.toLinAlgEquiv b ((s • B) ^ k) = (s • f) ^ k := by
    intro k
    rw [map_pow, map_smul, hB, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  have key : ∀ v : V, NormedSpace.exp (s • A) *ᵥ (v : Fin n → ℂ) =
      ((Matrix.toLinAlgEquiv b (NormedSpace.exp (s • B))) v : Fin n → ℂ) := by
    intro v
    open scoped Matrix.Norms.Operator in
    have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • A)
    open scoped Matrix.Norms.Operator in
    have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • B)
    let g1 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
      LinearMap.applyₗ (v : Fin n → ℂ) ∘ₗ Matrix.toLin'.toLinearMap
    let g2 : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
      V.subtype ∘ₗ LinearMap.applyₗ v ∘ₗ (Matrix.toLinAlgEquiv b).toLinearMap
    have h1' := h1.map g1 (LinearMap.continuous_of_finiteDimensional g1)
    have h2' := h2.map g2 (LinearMap.continuous_of_finiteDimensional g2)
    have heq : (g1 ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (s • A) ^ k) =
        (g2 ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (s • B) ^ k) := by
      funext k
      simp only [Function.comp_apply, map_smul, g1, g2, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        LinearEquiv.coe_coe, Matrix.toLin'_apply, AlgEquiv.toLinearMap_apply, Submodule.subtype_apply]
      rw [hpowA, hpowB]
    rw [heq] at h1'
    exact h1'.unique h2'
  have hstab : ∀ y ∈ V, Matrix.toLin' (NormedSpace.exp (s • A)) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply, key ⟨y, hy⟩]; exact Submodule.coe_mem _
  have hres : (Matrix.toLin' (NormedSpace.exp (s • A))).restrict hstab =
      Matrix.toLinAlgEquiv b (NormedSpace.exp (s • B)) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.restrict_coe_apply, Matrix.toLin'_apply]
    exact key v
  rw [detOn, dif_pos hstab, hres]
  show ‖LinearMap.det (Matrix.toLin b b (NormedSpace.exp (s • B)))‖ = _
  rw [LinearMap.det_toLin, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul, Complex.norm_exp, hs,
    Complex.re_ofReal_mul]

end GlobalTheory.FlagMeas
