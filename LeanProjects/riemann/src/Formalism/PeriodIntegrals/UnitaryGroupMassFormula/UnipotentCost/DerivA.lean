import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic

open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.DA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cd

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}

lemma cm_iff {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} :
    ContDiffAt ℝ n F x ↔ ∀ i j, ContDiffAt ℝ n (fun y => F y i j) x :=
  (contDiffAt_pi (Φ := F)).trans (forall_congr' fun _ => contDiffAt_pi)

lemma cm_mul {a b c : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} {G : X → Matrix (Fin b) (Fin c) ℂ}
    (hF : ContDiffAt ℝ n F x) (hG : ContDiffAt ℝ n G x) : ContDiffAt ℝ n (fun y => F y * G y) x := by
  rw [cm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hF i l).mul (hG l j)

lemma c_det {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y).det) x := by
  rw [cm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hF _ _)

lemma cm_updateRow {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (j : Fin a)
    (b : Fin a → ℂ) : ContDiffAt ℝ n (fun y => (F y).updateRow j b) x := by
  rw [cm_iff] at hF ⊢
  intro i l
  by_cases hi : i = j
  · subst hi; simp only [updateRow_self]; exact contDiffAt_const
  · simp only [updateRow_ne hi]; exact hF i l

lemma cm_inv {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (hu : (F x).det ≠ 0) :
    ContDiffAt ℝ n (fun y => (F y)⁻¹) x := by
  rw [cm_iff]
  intro i j
  have e : (fun y => (F y)⁻¹ i j)
      = fun y => ((F y).det)⁻¹ * ((F y).updateRow j (Pi.single i 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((c_det hF).inv hu).mul (c_det (cm_updateRow hF j _))

lemma cm_conjT {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y)ᴴ) x := by
  rw [cm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp x (hF j i)

lemma contDiffAt_block_matrix_two {p s : ℕ} {A : X → Matrix (Fin p) (Fin p) ℂ} {B' : X → Matrix (Fin p) (Fin s) ℂ}
    {C : X → Matrix (Fin s) (Fin p) ℂ} {D : X → Matrix (Fin s) (Fin s) ℂ}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B' x) (hC : ContDiffAt ℝ n C x) (hD : ContDiffAt ℝ n D x) :
    ContDiffAt ℝ n (fun y => blk2 (A y) (B' y) (C y) (D y)) x := by
  rw [cm_iff] at hA hB hC hD ⊢
  intro i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂] <;>
    first | exact hA _ _ | exact hB _ _ | exact hC _ _ | exact hD _ _

lemma contDiffAt_block_matrix_three {k j ρ : ℕ} {A11 : X → Matrix (Fin j) (Fin j) ℂ} {A12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : X → Matrix (Fin j) (Fin j) ℂ} {A21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : X → B.Mat k ρ}
    {A23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : X → Matrix (Fin j) (Fin j) ℂ}
    {A32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : ContDiffAt ℝ n A11 x) (h12 : ContDiffAt ℝ n A12 x) (h13 : ContDiffAt ℝ n A13 x)
    (h21 : ContDiffAt ℝ n A21 x) (h22 : ContDiffAt ℝ n A22 x) (h23 : ContDiffAt ℝ n A23 x)
    (h31 : ContDiffAt ℝ n A31 x) (h32 : ContDiffAt ℝ n A32 x) (h33 : ContDiffAt ℝ n A33 x) :
    ContDiffAt ℝ n (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y)) x := by
  rw [cm_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

end cd

section hd

variable {t : ℝ}

lemma hd_iff {a b : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {F' : Matrix (Fin a) (Fin b) ℂ} :
    HasDerivAt F F' t ↔ ∀ i j, HasDerivAt (fun y => F y i j) (F' i j) t :=
  (hasDerivAt_pi (φ := F)).trans (forall_congr' fun _ => hasDerivAt_pi)

lemma hd_mul {a b c : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {G : ℝ → Matrix (Fin b) (Fin c) ℂ}
    {F' : Matrix (Fin a) (Fin b) ℂ} {G' : Matrix (Fin b) (Fin c) ℂ}
    (hF : HasDerivAt F F' t) (hG : HasDerivAt G G' t) :
    HasDerivAt (fun y => F y * G y) (F' * G t + F t * G') t := by
  rw [hd_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun l _ => (hF i l).mul (hG l j)

lemma hasDerivAt_block_matrix_three {k j ρ : ℕ} {A11 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A12 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A21 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : ℝ → B.Mat k ρ}
    {A23 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {A32 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {ToralGalois : Matrix (Fin j) (Fin j) ℂ} {cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {B13 : Matrix (Fin j) (Fin j) ℂ} {B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B22 : B.Mat k ρ}
    {B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B31 : Matrix (Fin j) (Fin j) ℂ}
    {B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {B33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : HasDerivAt A11 ToralGalois t) (h12 : HasDerivAt A12 cocyclesToWachVectorsExponent t) (h13 : HasDerivAt A13 B13 t)
    (h21 : HasDerivAt A21 B21 t) (h22 : HasDerivAt A22 B22 t) (h23 : HasDerivAt A23 B23 t)
    (h31 : HasDerivAt A31 B31 t) (h32 : HasDerivAt A32 B32 t) (h33 : HasDerivAt A33 B33 t) :
    HasDerivAt (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y))
      (blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33) t := by
  rw [hd_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

lemma hd_invT {a : ℕ} (B : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) (-Bᴴ) 0 := by
  have hL : HasDerivAt (fun t : ℝ => (1 + t • B)ᴴ) Bᴴ 0 := by
    have e : (fun t : ℝ => (1 + t • B)ᴴ) = fun t => 1 + t • Bᴴ := by
      funext t; simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
    rw [e]
    exact (((hasDerivAt_id' (0 : ℝ)).smul_const Bᴴ).const_add (1 : Matrix (Fin a) (Fin a) ℂ)).congr_deriv (one_smul _ _)
  have hC : ContDiffAt ℝ 1 (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 :=
    cm_inv (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))) (by simp)
  have hCd := (hC.differentiableAt one_ne_zero).hasDerivAt
  have hP := hd_mul hCd hL
  have hcont : ContinuousAt (fun t : ℝ => ((1 + t • B)ᴴ).det) 0 :=
    (c_det (n := 0) (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)))).continuousAt
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 + t • B)ᴴ).det ≠ 0 := hcont.eventually_ne (by simp)
  have hev : (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) =ᶠ[𝓝 0] fun _ => 1 := by
    filter_upwards [hne] with t ht
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  have h0 : HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin a) (Fin a) ℂ)).congr_of_eventuallyEq hev
  have hu := h0.unique hP
  simp only [zero_smul, add_zero, Matrix.conjTranspose_one, inv_one, Matrix.mul_one, Matrix.one_mul] at hu
  have : deriv (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 = -Bᴴ := eq_neg_of_add_eq_zero_left hu.symm
  exact hCd.congr_deriv this

end hd

end PI.UnitaryGroupMassFormula.UsCost.DA
