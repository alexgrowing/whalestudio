import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne

set_option autoImplicit false

open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

namespace GlobalTheory.LieFilt

theorem det_eq_one_of_blockUni_elim {R : Type} [CommRing R] {κ : Type} [Fintype κ] (bl : κ → ℕ) (Q : Matrix κ κ R)
    (hQ : BlockUni bl Q) : Q.det = 1 := by
  have hT : Q.BlockTriangular bl := by
    intro i j hij
    rw [hQ i j (not_lt.mpr hij.le), Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have h1 : Q.toSquareBlock bl a = 1 := by
    ext i j
    have h : ¬ bl i.1 < bl j.1 := by rw [i.2, j.2]; exact lt_irrefl _
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hQ _ _ h, Matrix.one_apply, Matrix.one_apply]
    simp only [Subtype.ext_iff]
  rw [h1]
  convert Matrix.det_one

theorem exists_blockUni_mul_eq_zero {R : Type} [CommRing R] {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ}
    (P : Matrix (Fin g) κ R) (w : κ ≃ Fin g) (h : ∀ k : ℕ, IsUnit (minor bl w k P)) :
    ∃ Q : Matrix κ κ R, BlockUni bl Q ∧ Q.det = 1 ∧ ∀ z z', bl z < bl z' → (P * Q) (w z) z' = 0 := by
  let S : ∀ k : ℕ, Matrix {z // bl z < k} {z // bl z < k} R :=
    fun k => (P.submatrix w id).toSquareBlockProp fun z => bl z < k
  have hS : ∀ k, IsUnit (S k).det := h
  let v : ∀ z' : κ, {z // bl z < bl z'} → R := fun z' => (S (bl z'))⁻¹.mulVec fun y => P (w y.1) z'
  have hv : ∀ z', (S (bl z')).mulVec (v z') = fun y => P (w y.1) z' := by
    intro z'
    simp only [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hS _), Matrix.one_mulVec]
  let N : Matrix κ κ R := fun z z' => if hz : bl z < bl z' then v z' ⟨z, hz⟩ else 0
  have hQ : BlockUni bl (1 - N) := by
    intro z z' hz
    rw [Matrix.sub_apply]
    simp only [N, dif_neg hz, sub_zero]
  refine ⟨1 - N, hQ, det_eq_one_of_blockUni_elim bl _ hQ, fun z z' hz => ?_⟩
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, sub_eq_zero]
  have h1 := congrFun (hv z') ⟨z, hz⟩
  simp only at h1
  rw [← h1, Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun y => bl y < bl z')]
  have h2 : ∑ y : {y // ¬ bl y < bl z'}, P (w z) y.1 * N y.1 z' = 0 :=
    Finset.sum_eq_zero fun y _ => by simp only [N, dif_neg y.2, mul_zero]
  rw [h2, add_zero]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [N, dif_pos y.2]
  rfl

end GlobalTheory.LieFilt
