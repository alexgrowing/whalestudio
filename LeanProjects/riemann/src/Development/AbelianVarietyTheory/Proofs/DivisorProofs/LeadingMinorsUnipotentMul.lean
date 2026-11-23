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

namespace GlobalTheory.FlagCell

theorem lu_minor_gen {R : Type} [CommRing R] {m l : ℕ} (n : Low m → R) (M : Matrix (Fin m) (Fin m) R)
    (hM : M.BlockTriangular id) (e : Fin l → Fin m) (hmono : StrictMono e)
    (hout : ∀ k, k ∉ Set.range e → ∀ j, e j < k) :
    ((uniR n * M).submatrix e e).det = (M.submatrix e e).det := by
  have hsplit : (uniR n * M).submatrix e e = (uniR n).submatrix e e * M.submatrix e e := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e hmono.injective _ _ ?_ (fun _ => rfl)
    intro k hk
    have h0 : M k (e j) = 0 := hM (hout k hk j)
    rw [h0, mul_zero]
  have hU : ((uniR n).submatrix e e).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      rw [Matrix.submatrix_apply, uniR_apply, dif_neg (lt_irrefl _), if_pos rfl]
    · intro i j hij
      have hij' : i < j := hij
      have h2 : e i < e j := hmono hij'
      rw [Matrix.submatrix_apply, uniR_apply, dif_neg (not_lt.mpr h2.le), if_neg h2.ne]
  rw [hsplit, Matrix.det_mul, hU, one_mul]

theorem det_leading_uniR_mul : ∀ (R : Type) [CommRing R] (m : ℕ) (n : Low m → R) (M : Matrix (Fin m) (Fin m) R), M.BlockTriangular id → ∀ l : Fin (m + 1), ((uniR n * M).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det = (M.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
  intro R _ m n M hM l
  refine lu_minor_gen n M hM _ (Fin.strictMono_castLE _) ?_
  intro k hk j
  have hkl : l.1 ≤ k.1 := by
    by_contra hc
    exact hk ⟨⟨k.1, lt_of_not_ge hc⟩, Fin.ext rfl⟩
  rw [Fin.lt_def]
  exact lt_of_lt_of_le j.2 hkl

end GlobalTheory.FlagCell
