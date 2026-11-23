import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.FlagMeas.DetAdj

lemma mul_basisMat_eq {n : ℕ} (V : Submodule ℂ (Fin n → ℂ)) {d : Type} [Fintype d] [DecidableEq d]
    (b : Module.Basis d ℂ V) (g : Matrix (Fin n) (Fin n) ℂ) (f : V →ₗ[ℂ] V)
    (hf : ∀ v : V, ((f v : V) : Fin n → ℂ) = g *ᵥ (v : Fin n → ℂ)) :
    g * Matrix.of (fun i j => (b j : Fin n → ℂ) i) =
      Matrix.of (fun i j => (b j : Fin n → ℂ) i) * LinearMap.toMatrix b b f := by
  ext i j
  have h1 : (g * Matrix.of (fun i j => (b j : Fin n → ℂ) i)) i j = (g *ᵥ (b j : Fin n → ℂ)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, ← hf]
  have h2 : ((f (b j) : V) : Fin n → ℂ) = ∑ k, b.repr (f (b j)) k • (b k : Fin n → ℂ) := by
    conv_lhs => rw [← b.sum_repr (f (b j))]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [h2]
  simp [Matrix.mul_apply, LinearMap.toMatrix_apply, Finset.sum_apply, mul_comm]

theorem detOn_conjTranspose : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)),
    (∀ y ∈ V, g *ᵥ y ∈ V) → (∀ y ∈ V, gᴴ *ᵥ y ∈ V) →
      GlobalTheory.FlagMeas.detOn gᴴ V = GlobalTheory.FlagMeas.detOn g V := by
  intro n g V hg hgh
  have hg' : ∀ y ∈ V, Matrix.toLin' g y ∈ V := by simpa [Matrix.toLin'_apply] using hg
  have hgh' : ∀ y ∈ V, Matrix.toLin' gᴴ y ∈ V := by simpa [Matrix.toLin'_apply] using hgh
  unfold GlobalTheory.FlagMeas.detOn
  rw [dif_pos hgh', dif_pos hg']
  set f := (Matrix.toLin' g).restrict hg'
  set f' := (Matrix.toLin' gᴴ).restrict hgh'
  let b := Module.finBasis ℂ V
  set B : Matrix (Fin n) (Fin (Module.finrank ℂ V)) ℂ := Matrix.of (fun i j => (b j : Fin n → ℂ) i) with hB
  set A := LinearMap.toMatrix b b f
  set A' := LinearMap.toMatrix b b f'
  have h1 : g * B = B * A := mul_basisMat_eq V b g f (fun v => by simp [f, Matrix.toLin'_apply])
  have h2 : gᴴ * B = B * A' := mul_basisMat_eq V b gᴴ f' (fun v => by simp [f', Matrix.toLin'_apply])
  have hinj : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    have : B.col = fun j => (b j : Fin n → ℂ) := by ext j i; rfl
    rw [this]
    exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hG : (Bᴴ * B).det ≠ 0 := (Matrix.PosDef.conjTranspose_mul_self B hinj).det_pos.ne'
  have key : (Bᴴ * B) * A = A'ᴴ * (Bᴴ * B) := by
    calc (Bᴴ * B) * A = Bᴴ * (g * B) := by rw [h1, Matrix.mul_assoc]
      _ = (gᴴ * B)ᴴ * B := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = A'ᴴ * (Bᴴ * B) := by rw [h2, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hdet : A.det = star A'.det := by
    have := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_comm (star _)] at this
    exact mul_left_cancel₀ hG this
  rw [← LinearMap.det_toMatrix b f, ← LinearMap.det_toMatrix b f']
  change ‖A'.det‖ = ‖A.det‖
  rw [hdet, norm_star]

end GlobalTheory.FlagMeas.DetAdj
