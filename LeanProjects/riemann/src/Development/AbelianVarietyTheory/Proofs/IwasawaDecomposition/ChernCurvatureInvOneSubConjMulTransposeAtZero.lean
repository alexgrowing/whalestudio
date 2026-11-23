import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
open scoped Matrix

namespace GlobalTheory.HermFrame

open Matrix Filter Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [DecidableEq m] [Fintype l]

theorem curv_inv_one_sub_mul {P : E → Matrix m l ℂ} {Q : E → Matrix l m ℂ} {z ξ η : E}
    {C : Matrix l m ℂ} (hP : ∀ x, MContDiffAt 2 P x) (hQ : ∀ x, MContDiffAt 2 Q x)
    (hP0 : P z = 0) (hdP : ∀ x, mdel P x ξ = 0) (hdQ : ∀ x, mdel Q x ξ = C) :
    curv (fun x => (1 - P x * Q x)⁻¹) z ξ η = -(mdbar P z η * C)ᵀ := by
  have hK : ∀ x, MContDiffAt 2 (fun x => 1 - P x * Q x) x :=
    fun x => (mContDiffAt_const 1).sub ((hP x).mul (hQ x))
  have hK0 : (1 - P z * Q z) = 1 := by rw [hP0]; simp
  have hd : ∀ x, mdel (fun x => 1 - P x * Q x) x ξ = -(P x * C) := fun x => by
    have h1 := (hP x).of_le one_le_two
    have h2 := (hQ x).of_le one_le_two
    simp only [sub_eq_add_neg]
    rw [mdel_add (mContDiffAt_const 1) (h1.mul h2).neg, mdel_neg, mdel_mul h1 h2, hdP, hdQ]
    simp
  have hdd : mddbar (fun x => 1 - P x * Q x) z ξ η = -(mdbar P z η * C) := by
    rw [← mdbar_mdel (hK z)]
    simp only [hd]
    rw [mdbar_neg, mdbar_mul ((hP z).of_le one_le_two) (mContDiffAt_const C)]
    simp
  have hu : IsUnit (1 - P z * Q z)ᵀ.det := by rw [hK0]; simp
  have e : (fun x => (1 - P x * Q x)⁻¹) = fun x => dualGram (1 - P x * Q x)ᵀ := by
    funext x; rw [dualGram, transpose_nonsing_inv, transpose_transpose]
  rw [e, curv_dual (hK z).transpose hu, curv_eq (hK z).transpose hu,
    mdel_transpose (fun x => 1 - P x * Q x), hd,
    show mddbar (fun x => (1 - P x * Q x)ᵀ) z ξ η = (mddbar (fun x => 1 - P x * Q x) z ξ η)ᵀ from rfl,
    hdd, hK0, hP0]
  simp

end

section

variable {n : ℕ} {a b : Type*}

theorem mContDiffAt_coordMatrix (f : a → b → Fin n) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w := fun i j =>
  ((EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ).contDiff.contDiffAt

theorem mdel_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ =
      Matrix.of fun i j => ξ (f i j) := by
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ := EuclideanSpace.proj (𝕜 := ℂ) (f i j)
  change del L w ξ = L ξ
  rw [del_eq_fderiv L.differentiableAt, L.fderiv]

theorem mdbar_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ = 0 := by
  have h := mdel_add_mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ
  rw [mdel_coordMatrix] at h
  rw [← add_right_inj (Matrix.of fun i j => ξ (f i j)), h, add_zero]
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ
  change fderiv ℝ L w ξ = L ξ
  rw [L.fderiv]

end

theorem curv_inv_one_sub_conj_mul_transpose_zero : ∀ {n r s : ℕ} (f g : Fin r → Fin s → Fin n) (ξ η : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 ξ η = -((Matrix.of fun i j => ξ (g i j)) * (Matrix.of fun i j => η (f i j))ᴴ) := by
  intro n r s f g ξ η
  let Z : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (f i j)
  let W : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (g i j)
  have h := curv_inv_one_sub_mul (P := fun u => (Z u)ᴴᵀ) (Q := fun u => (W u)ᵀ) (z := 0) (ξ := ξ)
    (η := η) (C := (W ξ)ᵀ) (fun x => (mContDiffAt_coordMatrix f x).conjTranspose.transpose)
    (fun x => (mContDiffAt_coordMatrix g x).transpose) (by ext i j; simp [Z])
    (fun x => by
      rw [mdel_transpose (fun u => (Z u)ᴴ), mdel_conjTranspose, mdbar_coordMatrix]; simp)
    (fun x => by rw [mdel_transpose W, mdel_coordMatrix])
  rw [mdbar_transpose (fun u => (Z u)ᴴ), mdbar_conjTranspose, mdel_coordMatrix, ← transpose_mul,
    transpose_transpose] at h
  exact h

end GlobalTheory.HermFrame
