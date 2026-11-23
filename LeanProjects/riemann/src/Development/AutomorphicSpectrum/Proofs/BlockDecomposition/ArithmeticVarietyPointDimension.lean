import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KrullDimQuotientEqTrdegSuccStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionFieldOfPointCoordsTopStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimVar

open Topology

theorem finiteType_of_chart {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] {C : Type} [CommRing C]
    [Algebra ℤ C] (j : Spec (.of C) ⟶ Y) [IsOpenImmersion j] (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℤ C))) :
    Algebra.FiniteType ℤ C :=
  RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap ℤ C))).mp (hj ▸ inferInstance)

theorem topologicalKrullDim_closure_eq (Y : Scheme.{0}) (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] (y : Y)
    [CharZero (Y.residueField y)] :
    topologicalKrullDim (closure ({y} : Set Y)) =
      (((Algebra.trdeg ℤ (Y.residueField y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨B, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f y
  subst hq
  have := finiteType_of_chart f j hj
  rw [← GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance, ← topologicalKrullDim_range_inter_closure_eq j q]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun z ↦ ?_)
    (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  obtain ⟨C, _, _, j', _, y', hy, hj'⟩ := exists_affine_chart_over f z.1
  have := finiteType_of_chart f j' hj'
  obtain ⟨q', hq'⟩ := (specializes_iff_mem_closure.mpr z.2).mem_open
    j'.isOpenEmbedding.isOpen_range ⟨y', hy⟩
  refine ⟨Subtype.val ⁻¹' Set.range j',
    j'.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val, ⟨y', hy⟩, ?_⟩
  rw [← topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (Z := Set.range j' ∩ closure {j q})
    (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])]
  rw [topologicalKrullDim_range_inter_closure_eq j q, GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance]
  conv_lhs => rw [← hq', topologicalKrullDim_range_inter_closure_eq j' q']
  have h0 : CharZero (Y.residueField (j' q')) := hq' ▸ inferInstance
  rw [GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y C j' q' h0, hq']

theorem ptCoord_chart_ne_zero {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) (k : Fin (m + 1)) :
    ptCoord x ⟨k, ptChart x k⟩ ≠ 0 := by
  simp [ptCoord, pullRatio_self]

theorem isArithVar_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  intro m n x d hch hd
  have hdim := topologicalKrullDim_closure_eq (MP ℤ m n) (mpStr ℤ m n) x
  rw [hd] at hdim
  have h1 : ((d : ℕ∞)) = (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat + 1 := WithBot.coe_injective hdim
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat = t := by
    refine ⟨(Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat.toNat, (ENat.coe_toNat ?_).symm⟩
    intro h
    rw [h] at h1
    exact ENat.coe_ne_top d (by simpa using h1)
  have hdt : d = t + 1 := by
    rw [ht] at h1
    exact_mod_cast h1
  subst hdt
  have htr : Algebra.trdeg ℤ (blockFnField (ptCoord x)) = t := by
    rw [GlobalTheory.T.function_field_of_point_coords_top m n x, GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.trdeg_top]
    exact Cardinal.toENat_eq_nat.mp ht
  exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_of_trdeg (ptCoord x) (ptChart x) (ptCoord_chart_ne_zero x) t htr

end GlobalTheory.CompanionTheory.MPDict.DimVar
