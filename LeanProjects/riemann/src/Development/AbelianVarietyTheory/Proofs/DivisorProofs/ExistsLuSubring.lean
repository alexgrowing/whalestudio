import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentTriangularFactor

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagLU

theorem det_lead {K : Type} [CommRing K] {s : ℕ} (g : Matrix (Fin s) (Fin s) K) (l : ℕ) (hl : l ≤ s) :
    (g.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < l} → Fin s) Subtype.val).det := by
  let e : Fin l ≃ {a : Fin s // (a : ℕ) < l} :=
    { toFun := fun i => ⟨Fin.castLE hl i, i.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem exists_lu_subring : ∀ (K : Type) [Field K] (O : Subring K) (s : ℕ) (g : Matrix (Fin s) (Fin s) K), (∀ i j, g i j ∈ O) → (∀ k : ℕ, (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det ≠ 0 ∧ ((g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det)⁻¹ ∈ O) → ∃ (y : Low s → K) (b : Matrix (Fin s) (Fin s) K), (∀ j, y j ∈ O) ∧ (∀ i j, b i j ∈ O) ∧ (∀ i j, i < j → b i j = 0) ∧ g = b * upU y := by
  intro K _ O s g hg hmin
  let A : Matrix (Fin s) (Fin s) O := Matrix.of fun i j => ⟨g j i, hg j i⟩
  have hA : A.map O.subtype = gᵀ := by ext i j; rfl
  have hu : ∀ l : Fin (s + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
    intro l
    have h1 : ((A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det : K) =
        (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < l} → Fin s) Subtype.val).det := by
      have h2 := det_lead g l l.is_le
      rw [← O.coe_subtype, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hA,
        ← Matrix.transpose_submatrix, Matrix.det_transpose, h2]
    obtain ⟨h0, hi⟩ := hmin l
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, h1]
    exact mul_inv_cancel₀ h0
  obtain ⟨n, M, hM, -, hAe⟩ := GlobalTheory.FlagCell.exists_lu O s A hu
  refine ⟨fun j => n j, (M.map O.subtype)ᵀ, fun j => (n j).2, fun i j => (M j i).2, ?_, ?_⟩
  · intro i j hij
    show ((M j i : O) : K) = 0
    rw [hM (i := j) (j := i) hij]; rfl
  · have key : A.map O.subtype = (GlobalTheory.FlagCell.uniR n * M).map O.subtype := by rw [← hAe]
    rw [hA, Matrix.map_mul, GlobalTheory.FlagCell.map_uniR] at key
    have h3 : (upU fun j => (n j : K)) = (GlobalTheory.FlagCell.uniR fun j => O.subtype (n j))ᵀ := by
      ext a b
      simp only [upU, Matrix.of_apply, Matrix.transpose_apply, GlobalTheory.FlagCell.uniR_apply, eq_comm]
      rfl
    rw [h3, ← Matrix.transpose_mul, ← key, Matrix.transpose_transpose]

end GlobalTheory.FlagLU
