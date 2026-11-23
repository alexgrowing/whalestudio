import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PointEvaluationMultiplicativeTsum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.LatticePointCountBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.DerivSimilitudeCharAtOneEqTrace
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem entry_mem {E : Type} [Field E] [NumberField E] {a : ℕ} (l m : Fin a) (w : InfinitePlace E) :
    (fun x : Fin a → Cinf E => star (x l w) * x m w) ∈ poly E a := by
  have h1 : (fun x : Fin a → Cinf E => star (x l w)) ∈ poly E a :=
    Algebra.subset_adjoin ⟨⟨⟨fun x => star (x l w), fun x y => by simp⟩, fun c x => by simp⟩, rfl⟩
  have h2 : (fun x : Fin a → Cinf E => x m w) ∈ poly E a :=
    Algebra.subset_adjoin ⟨⟨⟨fun x => x m w, fun x y => by simp⟩, fun c x => by simp⟩, rfl⟩
  exact Subalgebra.mul_mem _ h1 h2

private theorem gauss_unit {E : Type} [Field E] [NumberField E] {a : ℕ} (k : Kinf E a) (x : Fin a → Cinf E) :
    gauss (x ᵥ* k.1) = gauss x := by
  obtain ⟨h1, -, h3, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  unfold gauss
  rw [h3, k.2.2, h1]

private theorem mom_cpt {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a)
    (L : AddSubgroup (Fin a → Af E)) (hL : IsLat L) (k : Kinf E a) (g : GA E a) :
    (mom L (g * infGL E a (Unitary.toUnits k))).1 = star k.1 * (mom L g).1 * k.1 := by
  ext i j w
  have hs := fun l m => ((UpperTheory.hermitian_space_geometric_estimate E a ha L hL).2 _ (entry_mem l m w)).1 g
  have hT := (UpperTheory.lattice_point_count_bound E a ha L).2.2 k g
  have hg := (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ (pg fun x => star (x i w) * x j w)).2.1 g (Unitary.toUnits k)
  have hk : sc (Unitary.toUnits k).val = 1 := (UpperTheory.deriv_similitudeChar_at_one_eq_trace E a).2.2.2.2 k
  have hv : (Unitary.toUnits k).val = k.1 := rfl
  have hp : ∀ x : Fin a → Cinf E, pg (fun x => star (x i w) * x j w) (x ᵥ* k.1) =
      ∑ m, ∑ l, star (k.1 l i w) * pg (fun x => star (x l w) * x m w) x * k.1 m j w := fun x => by
    simp only [pg, gauss_unit, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.mul_apply, star_sum, star_mul',
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hk, hv] at hg
  simp only [one_smul, hp] at hg
  rw [Summable.tsum_finsetSum fun m _ => summable_sum fun l _ => ((hs l m).mul_left _).mul_right _] at hg
  change mean L (fun x => star (x i w) * x j w) _ = _
  rw [mean, hT, hg]
  simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Finset.sum_mul, Finset.sum_div, Matrix.star_apply,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Summable.tsum_finsetSum fun l _ => ((hs l m).mul_left _).mul_right _, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tsum_mul_right, tsum_mul_left]
  change _ = _ * (gsum L (pg fun x => star (x l w) * x m w) g / _) * _
  rw [gsum]
  ring

private theorem ell_toL {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

theorem UpperTheory.hermitian_gaussian_moment_bound :
    DevCpt := by
  intro E _ _ _ a ha L hL k g
  have hm := mom_cpt ha L hL k g
  have hk : k.1 * star k.1 = 1 := k.2.2
  have he : ell E a (toL (mom L (g * infGL E a (Unitary.toUnits k))).1) = ell E a (toL (mom L g).1) := by
    rw [hm, ell_toL, ell_toL, Matrix.trace_mul_cycle, hk, one_mul]
  apply Subtype.ext
  change k.1 * ((mom L _).1 - _ • (1 : Matrix (Fin a) (Fin a) (Cinf E))) * star k.1 =
    (mom L g).1 - _ • (1 : Matrix (Fin a) (Fin a) (Cinf E))
  rw [he, hm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hk, ← mul_assoc, ← mul_assoc, hk, one_mul,
    mul_assoc, hk, mul_one]
