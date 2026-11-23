import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

open Filter Topology

noncomputable section

namespace GlobalTheory.Proof.theta_zero_one_lower_vanish

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ}

def lowerZero (n : ℕ) (i : Fin n) : Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∀ a, i < a → v a = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {u v} hu hv a h => by simp [hu a h, hv a h]
  smul_mem' := fun c v hv a h => by simp [hv a h]

theorem inv_mul_upper (A e : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (hmem : ∀ i, (fun a => e a i) ∈ Submodule.span ℂ {v : Fin n → ℂ | ∃ j ≤ i, v = fun a => A a j}) :
    (A⁻¹ * e).BlockTriangular id := by
  intro a i h
  have hle : Submodule.span ℂ {v : Fin n → ℂ | ∃ j ≤ i, v = fun a => A a j} ≤
      (lowerZero n i).comap (A⁻¹).mulVecLin := by
    rw [Submodule.span_le]
    rintro v ⟨j, hj, rfl⟩ b hb
    have h1 : (A⁻¹ * A) b j = (1 : Matrix (Fin n) (Fin n) ℂ) b j := by
      rw [nonsing_inv_mul _ hA]
    rw [mul_apply] at h1
    simp only [Matrix.mulVecLin_apply, mulVec, dotProduct]
    rw [h1, one_apply_ne]
    exact fun e' => absurd (e' ▸ hb) (not_lt.2 hj)
  have := hle (hmem i) a h
  simpa [Matrix.mulVecLin_apply, mulVec, dotProduct, mul_apply] using this

theorem inv_upper {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.BlockTriangular id) :
    T⁻¹.BlockTriangular id := by
  by_cases hu : IsUnit T.det
  · letI := invertibleOfIsUnitDet T hu
    exact blockTriangular_inv_of_blockTriangular hT
  · rw [nonsing_inv_apply_not_isUnit _ hu]
    exact fun _ _ _ => rfl

end GlobalTheory.Proof.theta_zero_one_lower_vanish

open GlobalTheory.Proof.theta_zero_one_lower_vanish in

theorem GlobalTheory.Proof.theta_zero_one_lower_vanish.thetaZeroOne_lower_eq_zero :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ k l η, k < l → thetaZeroOne e y η l k = 0 := by
  intro E _ _ _ _ _ ι _ n U H Y π A e _ hA he y hy k l η hkl
  classical
  have hYn : Y ∈ 𝓝 y := hA.isOpen.mem_nhds hy

  have hAh : ∀ a b, DifferentiableAt ℂ (fun x => A x a b) y := fun a b =>
    ((hA.hol_frame a b).contDiffAt hYn).differentiableAt (by simp)
  have hA1 : MContDiffAt 1 A y := fun a b =>
    (((hA.hol_frame a b).contDiffAt hYn).restrict_scalars ℝ).of_le (by simp)
  have he1 : MContDiffAt 1 e y := fun a b =>
    ((he.smooth a b).contDiffAt hYn).of_le (by simp)
  have hAu := hA.isUnit y hy
  set T : E → Matrix (Fin n) (Fin n) ℂ := fun x => (A x)⁻¹ * e x with hTdef
  have hT1 : MContDiffAt 1 T y := (hA1.inv hAu).mul he1
  have hTup : ∀ x ∈ Y, (T x).BlockTriangular id := fun x hx =>
    inv_mul_upper (A x) (e x) (hA.isUnit x hx) (he.mem x hx)
  have heq : e =ᶠ[𝓝 y] fun x => A x * T x := Filter.mem_of_superset hYn fun x hx => by
    simp only [Set.mem_setOf_eq, hTdef, ← Matrix.mul_assoc, mul_nonsing_inv _ (hA.isUnit x hx),
      Matrix.one_mul]
  have hAbar : mdbar A y η = 0 := by
    ext a b; simp [dbar_eq_zero (hAh a b)]
  have hTbar : (mdbar T y η).BlockTriangular id := by
    intro a b hab
    rw [mdbar_apply, dbar_congr (g := fun _ => (0 : ℂ))
      (Filter.mem_of_superset hYn fun x hx => hTup x hx hab)]
    simp
  have hebar : mdbar e y η = A y * mdbar T y η := by
    rw [mdbar_congr heq, mdbar_mul hA1 hT1, hAbar, Matrix.zero_mul, add_zero]
  have hth : thetaZeroOne e y η = (T y)⁻¹ * mdbar T y η := by
    have hey : e y = A y * T y := heq.self_of_nhds
    rw [thetaZeroOne, hebar, hey, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (A y)⁻¹, nonsing_inv_mul _ hAu, Matrix.one_mul]
  rw [hth]
  exact ((inv_upper (hTup y hy)).mul hTbar) hkl
