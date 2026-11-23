import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

abbrev Vr (n : ℕ) := Fin n → Fin n → ℝ

def hermLin (n : ℕ) : Vr n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := herm
  map_add' x y := by
    ext i j
    simp only [herm, Pi.add_apply, Matrix.add_apply]
    push_cast
    ring
  map_smul' c x := by
    ext i j
    simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring

def hermL (n : ℕ) : Vr n →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap (hermLin n)

theorem hermL_apply (x : Vr n) : hermL n x = herm x := rfl

theorem herm_zero : herm (0 : Vr n) = 0 := by
  ext i j; simp [herm]

def v1 (r c : Fin n) : Vr n := fun i j =>
  ((if i = r ∧ j = c then 1 else 0) + (if i = c ∧ j = r then 1 else 0)) / 2

def v2 (r c : Fin n) : Vr n := fun i j =>
  ((if i = c ∧ j = r then 1 else 0) - (if i = r ∧ j = c then 1 else 0)) / 2

theorem herm_v (r c : Fin n) : herm (v1 r c) + Complex.I • herm (v2 r c) = Matrix.single r c 1 := by
  ext i j
  have e1 : (if j = r ∧ i = c then (1:ℝ) else 0) = if i = c ∧ j = r then 1 else 0 := by
    simp only [and_comm]
  have e2 : (if j = c ∧ i = r then (1:ℝ) else 0) = if i = r ∧ j = c then 1 else 0 := by
    simp only [and_comm]
  have e3 : (Matrix.single r c (1:ℂ)) i j = (((if i = r ∧ j = c then (1:ℝ) else 0 : ℝ)) : ℂ) := by
    rw [Matrix.single_apply]
    by_cases h : i = r ∧ j = c
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e3]
  simp only [herm, v1, v2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]
  generalize (if i = r ∧ j = c then (1:ℝ) else 0) = a
  generalize (if i = c ∧ j = r then (1:ℝ) else 0) = b
  push_cast
  linear_combination ((b:ℂ) - a) / 2 * Complex.I_sq

def dc (a : Fin n × Fin n) (f : Vr n → ℂ) : Vr n → ℂ :=
  fun x => fderiv ℝ f x (v1 a.1 a.2) + Complex.I * fderiv ℝ f x (v2 a.1 a.2)

def dList : List (Fin n × Fin n) → (Vr n → ℂ) → Vr n → ℂ
  | [], f => f
  | a :: l, f => dc a (dList l f)

end STD

end PositivityTheory.Rg.Sw.LVs
