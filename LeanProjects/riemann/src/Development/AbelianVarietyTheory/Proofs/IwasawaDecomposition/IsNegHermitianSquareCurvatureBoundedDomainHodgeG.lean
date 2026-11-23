import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign.DomCurv

section Sqrt

open scoped MatrixOrder

theorem exists_eq_conjTranspose_mul_self {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin k) (Fin k) ℂ, T = Bᴴ * B := by
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

end Sqrt

variable {m r : ℕ}

def domForm (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - Matrix.of x * (Matrix.of x)ᴴ

theorem domGram_eq (x : Fin m → Fin r → ℂ) : domGram m r x = ((domForm m r x)⁻¹)ᵀ := rfl

theorem mContDiffAt_of (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) y := fun a b => by
  show ContDiffAt ℝ k (fun x : Fin m → Fin r → ℂ => x a b) y
  exact ((contDiff_apply ℝ ℂ b).comp (contDiff_apply ℝ (Fin r → ℂ) a)).contDiffAt

theorem mdel_of (y ξ : Fin m → Fin r → ℂ) :
    mdel (fun y : Fin m → Fin r → ℂ => Matrix.of y) y ξ = Matrix.of ξ := by
  ext a b
  show del (fun x : Fin m → Fin r → ℂ => x a b) y ξ = ξ a b
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, del_eq_fderiv (ContinuousLinearMap.differentiableAt _), ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_of (y η : Fin m → Fin r → ℂ) :
    mdbar (fun y : Fin m → Fin r → ℂ => Matrix.of y) y η = 0 := by
  ext a b
  show dbar (fun x : Fin m → Fin r → ℂ => x a b) y η = 0
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem mContDiffAt_domForm (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (domForm m r) y :=
  (mContDiffAt_const 1).sub ((mContDiffAt_of k y).mul (mContDiffAt_of k y).conjTranspose)

theorem domForm_eq_fun : domForm m r = fun y => 1 + -(Matrix.of y * (Matrix.of y)ᴴ) := by
  funext y; simp [domForm, sub_eq_add_neg]

theorem mdel_domForm (y ξ : Fin m → Fin r → ℂ) :
    mdel (domForm m r) y ξ = -(Matrix.of ξ * (Matrix.of y)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdel_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdel_const,
    mdel_neg, mdel_mul h1 h1.conjTranspose, mdel_conjTranspose, mdbar_of, mdel_of]
  simp

theorem mdbar_domForm (y η : Fin m → Fin r → ℂ) :
    mdbar (domForm m r) y η = -(Matrix.of y * (Matrix.of η)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdbar_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdbar_const,
    mdbar_neg, mdbar_mul h1 h1.conjTranspose, mdbar_conjTranspose, mdbar_of, mdel_of]
  simp

theorem conn_domGram {y : Fin m → Fin r → ℂ} (hu : IsUnit (domForm m r y).det)
    (ξ : Fin m → Fin r → ℂ) :
    conn (domGram m r) y ξ = Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) := by
  have e : (fun x => (domGram m r x)ᵀ) = fun x => (domForm m r x)⁻¹ := by
    funext x; rw [domGram_eq, transpose_transpose]
  have e2 : (domGram m r y)ᵀ = (domForm m r y)⁻¹ := congrFun e y
  rw [conn, e2, ← mdel_transpose, e, mdel_inv (mContDiffAt_domForm 1 y) hu, mdel_domForm,
    nonsing_inv_nonsing_inv _ hu]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]

theorem curv_domGram_eq {x : Fin m → Fin r → ℂ} (hx : IsUnit (domForm m r x).det)
    (ξ η : Fin m → Fin r → ℂ) :
    curv (domGram m r) x ξ η = -(Matrix.of ξ * ((1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ *
      Matrix.of x) * ((Matrix.of η)ᴴ * (domForm m r x)⁻¹))) := by
  have hev := (mContDiffAt_domForm (m := m) (r := r) 1 x).eventually_isUnit hx
  have he : (fun y => conn (domGram m r) y ξ) =ᶠ[𝓝 x]
      fun y => Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) :=
    hev.mono fun y hy => conn_domGram hy ξ
  have hZ := mContDiffAt_of (m := m) (r := r) 1 x
  have hM := (mContDiffAt_domForm (m := m) (r := r) 1 x).inv hx
  rw [curv, mdbar_congr he, mdbar_mul (mContDiffAt_const (Matrix.of ξ)) (hZ.conjTranspose.mul hM),
    mdbar_const, mdbar_mul hZ.conjTranspose hM, mdbar_inv (mContDiffAt_domForm 1 x) hx,
    mdbar_domForm, mdbar_conjTranspose, mdel_of]
  simp only [Matrix.zero_mul, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_add]
  rw [add_comm]

end GlobalTheory.PointFormSign.DomCurv

namespace GlobalTheory.PointFormSign

open DomCurv in

theorem curv_domGram_isNegSq (m r : ℕ) (x : Fin m → Fin r → ℂ)
    (hx : (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef) : IsNegSq (curv (domGram m r) x) r := by
  have hxA : (domForm m r x).PosDef := hx
  have hu : IsUnit (domForm m r x).det := (isUnit_iff_isUnit_det _).1 hxA.isUnit
  have hM := hxA.inv
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul_self hM.posSemidef
  have hQ : (1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ * Matrix.of x).PosSemidef :=
    (PosDef.one.add_posSemidef (hM.posSemidef.conjTranspose_mul_mul_same (Matrix.of x))).posSemidef
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hQ
  have hBu : IsUnit B.det := by
    have h1 : IsUnit (Bᴴ * B).det := by rw [← hB]; exact (isUnit_iff_isUnit_det _).1 hM.isUnit
    rw [det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  let T : (Fin m → Fin r → ℂ) →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ :=
    { toFun := fun ξ => B * Matrix.of ξ * Cᴴ
      map_add' := fun ξ ξ' => by
        show B * Matrix.of (ξ + ξ') * Cᴴ = B * Matrix.of ξ * Cᴴ + B * Matrix.of ξ' * Cᴴ
        rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c ξ => by
        show B * (c • Matrix.of ξ) * Cᴴ = c • (B * Matrix.of ξ * Cᴴ)
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  refine ⟨B, T, hBu, fun ξ η => ?_⟩
  rw [curv_domGram_eq hu, hC, hB]
  show -(Matrix.of ξ * ((Cᴴ * C) * ((Matrix.of η)ᴴ * (Bᴴ * B)))) =
    B⁻¹ * (-((B * Matrix.of ξ * Cᴴ) * (B * Matrix.of η * Cᴴ)ᴴ)) * B
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hBu]

end GlobalTheory.PointFormSign
