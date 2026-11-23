import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormUniformizerConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsNormalProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsNormalProjectiveCoveringStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem princSt_of_connSt_propZ_densSt : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → DensSt → PrincSt := by
  intro hConn hZ hDens F _ _ V p _ hp X s Xw hXi hXn hproj hflat hXw hirr K hK hU
  by_cases hT : ∃ yb, IsTest p Xw yb
  swap
  · exact ⟨0, fun yb h => absurd ⟨yb, h⟩ hT⟩
  obtain ⟨yb₀, hyb₀⟩ := hT
  have hne : (Xw : Set X).Nonempty := (Set.range_nonempty _).mono hyb₀.2
  haveI : IsDiscreteValuationRing V :=
    (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V (Fact.out : p.Prime).ne_zero hp).1
  obtain ⟨D, hD, ht, sig, hsig, hval⟩ := GlobalTheory.T.exists_charts_normal_projective_covering GlobalTheory.T.exists_charts_normal_projective hDens F V p hp X s Xw hXi hXn hproj hflat hXw hne K hK hU
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hprop : IsProper s := by
    obtain ⟨N, i, hi, hs⟩ := hproj
    have := isProper_str V N
    rw [← hs]
    infer_instance
  have hHyp : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.Hyp s D :=
    ⟨hXi, fun z => (hXn z).2, hprop, hflat, hConn F V X s Xw hXi hXn hproj hflat hirr, hD, ht⟩
  obtain ⟨M, n, hM, -, hVC⟩ := hZ V ϖ hϖ X s D hHyp sig hsig
  obtain ⟨r, hr⟩ := GlobalTheory.T.norm_uniformizer_constant F V p hp ϖ hϖ
  refine ⟨(r ^ n) ^ ((M : ℝ)⁻¹), fun yb hyb κ hκ => ?_⟩
  obtain ⟨φ, hφi, hφl, hφs, y, hy⟩ := GlobalTheory.T.test_point_generic_fibre F V p hp X s Xw hXw yb hyb
  obtain ⟨⟨e, cc, he, hco⟩, hall⟩ := hVC 𝓞_ℂ_[p] ℂ_[p] ℝ≥0 (Valued.v : Valuation ℂ_[p] ℝ≥0)
    (PadicComplexInt.integers p) φ hφi hφl yb hφs y hy
  have h1 := hall e cc he hco
  have h2 := hval yb hyb y hy e cc he hco κ hκ
  have h3 : ‖(cc : ℂ_[p])‖ ^ M = r ^ n := by
    have := congrArg (fun t : ℝ≥0 => (t : ℝ)) h1
    simp only [NNReal.coe_pow, NNReal.coe_zpow, coe_valued] at this
    rw [this, ← hr φ]
    rfl
  rw [← h2, ← h3, Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega)]

end GlobalTheory.FlatModel
