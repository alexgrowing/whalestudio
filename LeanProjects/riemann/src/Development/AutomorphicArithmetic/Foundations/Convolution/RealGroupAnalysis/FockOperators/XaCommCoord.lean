import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwShift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PForm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoordMk

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section Abstract

variable {A : Type*} [Ring A] [Algebra ℂ A]

private def Xa (θ : ℂ) (x : Fin 4 → A) : Fin 2 → Fin 2 → A :=
  ![![x 1, x 2 + θ • x 3], ![x 2 - θ • x 3, x 0]]

private noncomputable def Da (θ : ℂ) (d : Fin 4 → A) : Fin 2 → Fin 2 → A :=
  ![![d 1, (2 : ℂ)⁻¹ • (d 2 + θ⁻¹ • d 3)], ![(2 : ℂ)⁻¹ • (d 2 - θ⁻¹ • d 3), d 0]]

private lemma Xa_comm_coord (θ : ℂ) {x y : Fin 4 → A} (h : ∀ i j, Commute (x i) (y j)) (a b : Fin 2) (j : Fin 4) :
    Commute (Xa θ x a b) (y j) := by
  fin_cases a <;> fin_cases b
  · exact h 1 j
  · exact (h 2 j).add_left ((h 3 j).smul_left θ)
  · exact (h 2 j).sub_left ((h 3 j).smul_left θ)
  · exact h 0 j

private lemma Xa_comm (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b c d : Fin 2) :
    Commute (Xa θ x a b) (Xa θ x c d) := by
  have h' := Xa_comm_coord θ h a b
  fin_cases c <;> fin_cases d
  · exact h' 1
  · exact (h' 2).add_right ((h' 3).smul_right θ)
  · exact (h' 2).sub_right ((h' 3).smul_right θ)
  · exact h' 0

private lemma Da_comm_coord (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b : Fin 2) (j : Fin 4) :
    Commute (Da θ x a b) (x j) := by
  fin_cases a <;> fin_cases b
  · exact h 1 j
  · exact ((h 2 j).add_left ((h 3 j).smul_left θ⁻¹)).smul_left _
  · exact ((h 2 j).sub_left ((h 3 j).smul_left θ⁻¹)).smul_left _
  · exact h 0 j

private lemma Da_comm (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b c d : Fin 2) :
    Commute (Da θ x a b) (Da θ x c d) := by
  have h' := Da_comm_coord θ h a b
  fin_cases c <;> fin_cases d
  · exact h' 1
  · exact ((h' 2).add_right ((h' 3).smul_right θ⁻¹)).smul_right _
  · exact ((h' 2).sub_right ((h' 3).smul_right θ⁻¹)).smul_right _
  · exact h' 0

private lemma Da_Xa (θ : ℂ) (hθ : θ ≠ 0) {x d : Fin 4 → A}
    (hw : ∀ i j, d i * x j = x j * d i + if i = j then 1 else 0) (a b c e : Fin 2) :
    Da θ d a b * Xa θ x c e = Xa θ x c e * Da θ d a b + if a = c ∧ b = e then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp only [Xa, Da, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, hw] <;>
    simp <;> match_scalars <;> field_simp <;> ring

private lemma Xa_det (θ c : ℂ) (hc : θ ^ 2 = c) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) :
    Xa θ x 0 1 * Xa θ x 1 0 - Xa θ x 0 0 * Xa θ x 1 1 = x 2 * x 2 - c • (x 3 * x 3) - x 1 * x 0 := by
  have h32 : x 3 * x 2 = x 2 * x 3 := h 3 2
  subst hc
  simp only [Xa, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, h32]
  match_scalars <;> ring

private lemma Da_det (θ c : ℂ) (hθ : θ ≠ 0) (hc : θ ^ 2 = c) {d : Fin 4 → A} (h : ∀ i j, Commute (d i) (d j)) :
    Da θ d 0 1 * Da θ d 1 0 - Da θ d 0 0 * Da θ d 1 1 =
      (4 : ℂ)⁻¹ • (d 2 * d 2) - (4 * c)⁻¹ • (d 3 * d 3) - d 1 * d 0 := by
  have h32 : d 3 * d 2 = d 2 * d 3 := h 3 2
  subst hc
  simp only [Da, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, h32]
  match_scalars <;> field_simp <;> ring

private lemma Xa_Da_sum (θ : ℂ) (hθ : θ ≠ 0) (x d : Fin 4 → A) :
    ∑ a, ∑ b, Xa θ x a b * Da θ d a b = ∑ i, x i * d i := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_four, Xa, Da, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  match_scalars <;> field_simp <;> ring

end Abstract

theorem UpperTheory.ConvolutionTheory.R2.Fo.weylX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (τ : E →+* ℂ),
    (∀ a b c d, O.X D τ a b * O.X D τ c d = O.X D τ c d * O.X D τ a b) ∧ (∀ a b c d, O.DX D τ a b * O.DX D τ c d = O.DX D τ c d * O.DX D τ a b) ∧
    (∀ a b c d, O.DX D τ a b * O.X D τ c d = O.X D τ c d * O.DX D τ a b + if a = c ∧ b = d then 1 else 0) ∧
    O.e D.δ (pl F τ) = cc • (O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1) ∧
    O.f D.δ (pl F τ) = (-cc⁻¹) • (O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1) ∧
    O.h (pl F τ) = (∑ a, ∑ b, O.X D τ a b * O.DX D τ a b) + 2 := by
  intro F E _ _ _ _ _ _ _ D W O τ
  obtain ⟨hsq, -, hθ⟩ := (coordMk F E D).2.1 τ
  have hx : ∀ i j, Commute (O.x (pl F τ) i) (O.x (pl F τ) j) := fun i j => (weyl F O _ _ i j).1
  have hd : ∀ i j, Commute (O.d (pl F τ) i) (O.d (pl F τ) j) := fun i j => dComm F E D W O _ _ i j
  have hw : ∀ i j, O.d (pl F τ) i * O.x (pl F τ) j = O.x (pl F τ) j * O.d (pl F τ) i + if i = j then 1 else 0 := by
    intro i j
    simpa using (weyl F O (pl F τ) (pl F τ) i j).2
  have eX : O.X D τ = Xa (τ D.θ) (O.x (pl F τ)) := rfl
  have eD : O.DX D τ = Da (τ D.θ) (O.d (pl F τ)) := rfl
  rw [eX, eD]
  refine ⟨fun a b c d => Xa_comm _ hx a b c d, fun a b c d => Da_comm _ hd a b c d,
    fun a b c d => Da_Xa _ hθ hw a b c d, ?_, ?_, ?_⟩
  · rw [Xa_det _ _ hsq hx]; rfl
  · rw [Da_det _ _ hθ hsq hd]; rfl
  · rw [Xa_Da_sum _ hθ]; rfl
