import Mathlib
import Formalism.FormalDegreeBessel.StatementBF

open Matrix MeasureTheory Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.BesselUnitary

def partner (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

lemma gram_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = partner k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk partner
  split_ifs <;> simp only [Fin.ext_iff] at * <;> first | rfl | omega

lemma gram_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner k r i)]
  · rw [gram_apply, gram_apply, Matrix.one_apply, if_pos rfl]
    unfold partner
    split_ifs <;> simp only [Fin.ext_iff] at * <;> first | omega | (simp; done) | (split_ifs <;> first | omega | simp)
  · intro b _ hb
    rw [gram_apply k r i b, if_neg hb, zero_mul]
  · simp

lemma isUnit_det_of_mem {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have h : (Hpk k r * (gᴴ * Hpk k r)) * g = 1 := by
    rw [mul_assoc, show gᴴ * Hpk k r * g = Hpk k r from hg, gram_sq]
  exact Matrix.isUnit_det_of_left_inverse h

lemma inv_mulVec_fixed {m : ℕ} {g : Matrix (Fin m) (Fin m) ℂ} (hg : IsUnit g.det) {v : Fin m → ℂ}
    (hv : g *ᵥ v = v) : g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← hv]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hg, Matrix.one_mulVec]

lemma inv_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g⁻¹ ∈ UWset k r z := by
  have hu := isUnit_det_of_mem hg.1
  refine ⟨?_, fun a => ⟨inv_mulVec_fixed hu (hg.2.1 a).1, inv_mulVec_fixed hu (hg.2.1 a).2⟩,
    inv_mulVec_fixed hu hg.2.2⟩
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg.1
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [h1]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
    _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ hu]; simp

def mulEquiv {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := a * Matrix.of x * b
  invFun x := a⁻¹ * Matrix.of x * b⁻¹
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * b) * b⁻¹ = Matrix.of x
    rw [← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ ha, one_mul, mul_assoc,
      Matrix.mul_nonsing_inv _ hb, mul_one]
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * b⁻¹) * b = Matrix.of x
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ ha, one_mul, mul_assoc,
      Matrix.nonsing_inv_mul _ hb, mul_one]
  measurable_toFun := by
    refine Continuous.measurable ?_
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  measurable_invFun := by
    refine Continuous.measurable ?_
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def repEquiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (W →L[ℂ] W)}
    (hπ : IsCRepOn (UWset k r z) π) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : W ≃L[ℂ] W :=
  ContinuousLinearEquiv.equivOfInverse (π h) (π h⁻¹)
    (fun x => by
      have := hπ.2 _ (inv_mem hh) _ hh
      rw [Matrix.nonsing_inv_mul _ (isUnit_det_of_mem hh.1), hπ.1] at this
      exact (congrArg (fun T : W →L[ℂ] W => T x) this).symm)
    (fun x => by
      have := hπ.2 _ hh _ (inv_mem hh)
      rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_mem hh.1), hπ.1] at this
      exact (congrArg (fun T : W →L[ℂ] W => T x) this).symm)

end GlobalTheory.BesselUnitary

namespace GlobalTheory

open BesselUnitary

end GlobalTheory
