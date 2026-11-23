import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShareStatementOfKnownTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValuationMultiplicityOfConsecutiveRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermitianPairingBilinearOnPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftsAndAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtBigRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement

set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem share_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative →
    _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition := by
  intro hX hP hSI hKS hG hQ hSL hDG hS hF hD
  have h1 := hS
  have h2 := hF
  have h3 := hD
  have h4 := _root_.GlobalTheory.T.size_bounds_for_family_alt hS
  have h5 := _root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt hP hG hQ hSI hKS hSL hDG hS hF
  have h6 := _root_.GlobalTheory.T.birOn_weightPair_both_components_alt hX hG hQ hSI hP hS
  unfold _root_.GlobalTheory.CovTop.SizeCondition at h1
  unfold _root_.GlobalTheory.CovTop.FlatDegreeCondition _root_.GlobalTheory.CovTop.CoversCondition at h2
  unfold _root_.GlobalTheory.CovTop.CoverDegree _root_.GlobalTheory.CovTop.CoversCondition at h3
  unfold _root_.GlobalTheory.CovTop.CoversCondition at h4 h5 h6
  have all := _root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h1 h2) (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h3 _root_.GlobalTheory.HSApp.wtBig_run_alt))
    (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS) h4)) (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h5 h6)
  clear h1 h2 h3 h4 h5 h6
  refine Closed.imp all fun Fm _ _ ⟨C, hC, x0, h⟩ => ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY u1 hu Z => ?_⟩
  obtain ⟨⟨_, ⟨_, ⟨_, ⟨_, hs⟩, _, hfl⟩, _, ⟨_, hdg⟩, _, hB⟩, _, ⟨_, hq⟩, _, hz⟩, _, ⟨_, hv⟩, _, hbi⟩ := h x hx hle ι p hp i
  obtain ⟨hp1, hq1, hf, hqu, hsa, ⟨w, -, hw⟩, hdom⟩ := hq hi
  obtain ⟨hT, hj, -⟩ := hz hi Y hY
  obtain ⟨-, h0, -, hz1⟩ := (hs.2.2.2.2.2.2 hi).2 u1 hu
  obtain ⟨δ, hδ, hδ2⟩ := hdg hi Y hY u1 hu
  obtain rfl := hqu u1 hu
  have htw := (_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hT _ hp1 hq1 hf hj Y _ _ hY.1 _ (hfl hi Y hY)).1
  refine ⟨?_, ?_⟩
  · rw [hw, htw]
    exact _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_lower_bound hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) Z (hbi hi Y hY Z).1
  · have hD2 : (2 : ℝ) ≤ CompHt.dimFlag (dat p i) := by
      rw [GlobalTheory.CompHS.dimFlag_eq]; exact_mod_cast two_le_dimFlag hp1 hq1 hf
    refine _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_upper_bound hX hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) hsa (fun Z => (hbi hi Y hY Z).1) (hv hi Y hY) h0 ?_ (uM p i) (fun τ => ?_) (fun τ => ?_) Z
      (hδ.trans_le (hδ2 Z).1)
    · unfold zed at hz1
      have : 0 ≤ (CompHt.dimFlag (dat p i) : ℝ) ^ 2 / lenT p i (Fm.parT x hx ι).PP := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hD2 h0]
    · simpa using (hdom 0 (by norm_num) τ).1
    · simpa using (hdom 0 (by norm_num) τ).2
end GlobalTheory.CovTop.ShareRowsNef
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.share_of_deep_good_size_flat_deg_cover_degree : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition := by
  first | exact @_root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt | exact _root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt <;> assumption)
end
end
