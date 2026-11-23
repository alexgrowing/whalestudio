import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveAndExistsFrameMulUpper
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagCell

theorem Spans.mul_upper : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl : Vert.Flag F m) (V : X.Opens) (v : Fin m → Γ(F, V)) (M : Matrix (Fin m) (Fin m) Γ(X, V)), Spans fl V v → M.BlockTriangular id → IsUnit M.det → Spans fl V fun j => ∑ k, M k j • v k := by
  intro X F m fl V v M hs hM hu l
  obtain ⟨s, hf, hι⟩ := hs l
  have hb : ∀ i j : Fin m, j < i → M i j = 0 := fun i j h => hM h
  refine ⟨_, GlobalTheory.FlagZ.Univ.isFrame_sum_smul_of_isUnit hf _
    (GlobalTheory.FlagZ.Loc.isUnit_submatrix_castLE_of_upper l.is_le M hb
      ((Matrix.isUnit_iff_isUnit_det M).2 hu)), fun j => ?_⟩
  rw [← GlobalTheory.QCoh.appLinear_apply]
  simp only [map_sum, map_smul, GlobalTheory.QCoh.appLinear_apply, hι, Matrix.submatrix_apply]
  refine Finset.sum_of_injOn (Fin.castLE l.is_le) (Fin.castLE_injective _).injOn
    (fun _ _ => Finset.mem_univ _) (fun k _ hk => ?_) (fun _ _ => rfl)
  rw [hb, zero_smul]
  by_contra hlt
  have hk' : (k : ℕ) < l := lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hlt)) j.2
  exact hk ⟨⟨k, hk'⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩

end GlobalTheory.FlagCell
