import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false

namespace GlobalTheory.FlagCell

theorem uniR_lowerTri {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) :
    (uniR n).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  simp only [uniR_apply]
  rw [dif_neg (not_lt.mpr hij'.le), if_neg (ne_of_lt hij')]

theorem uniR_diag {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) (i : Fin m) :
    uniR n i i = 1 := by
  simp [uniR_apply]

theorem uniR_det {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) : (uniR n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (uniR_lowerTri n)]
  simp [uniR_diag]

theorem uniR_unique_of_mul_eq (R : Type) [CommRing R] (m : ℕ) (n n' : Low m → R)
    (M M' : Matrix (Fin m) (Fin m) R) (hM : M.BlockTriangular id) (hM' : M'.BlockTriangular id)
    (hdet : IsUnit M.det) (h : uniR n * M = uniR n' * M') : n = n' := by
  set L := uniR n
  set L' := uniR n'
  have hL' : IsUnit L'.det := by rw [uniR_det]; exact isUnit_one
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hdet
  letI : Invertible L' := Matrix.invertibleOfIsUnitDet L' hL'
  have hP : L'⁻¹ * L = M' * M⁻¹ := by
    calc L'⁻¹ * L = L'⁻¹ * (L * M) * M⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = L'⁻¹ * (L' * M') * M⁻¹ := by rw [h]
      _ = M' * M⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hL', Matrix.one_mul]
  have hlow : (L'⁻¹ * L).BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular (uniR_lowerTri n')).mul (uniR_lowerTri n)
  have hup : (M' * M⁻¹).BlockTriangular id :=
    hM'.mul (Matrix.blockTriangular_inv_of_blockTriangular hM)
  set P := L'⁻¹ * L with hPdef
  have hdiag : P = Matrix.diagonal (fun j => P j j) := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hij)]
      exact hlow hij
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hij), hP]
      exact hup hij
  have hLP : L = L' * P := by
    rw [hPdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hL', Matrix.one_mul]
  have hP1 : ∀ j, P j j = 1 := by
    intro j
    have := congrFun (congrFun hLP j) j
    rw [hdiag, Matrix.mul_diagonal] at this
    simpa [L, L', uniR_diag] using this.symm
  have hLL : L = L' := by
    rw [hLP, hdiag]
    simp [hP1]
  funext s
  have := congrFun (congrFun hLL s.1.1) s.1.2
  simpa [L, L', uniR_apply, s.2] using this

end GlobalTheory.FlagCell
