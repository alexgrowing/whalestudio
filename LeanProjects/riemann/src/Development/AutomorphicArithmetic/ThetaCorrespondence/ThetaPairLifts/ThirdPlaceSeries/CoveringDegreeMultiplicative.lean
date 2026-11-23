import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDegreeMultiplicative
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValuationMultiplicityOfConsecutiveRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtBigRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement

set_option synthInstance.maxHeartbeats 200000

section
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
set_option autoImplicit false
namespace GlobalTheory.CovTop.DegProof
set_option maxHeartbeats 1000000 in
theorem covering_degree_eq_alt : HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree := by
  intro hX h2 hS hT hG hQ hN hDG hSz hF
  have hP := _root_.GlobalTheory.T.covering_topology_refinement h2
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt h2 hG hQ hS hT hN hDG hSz hF) _root_.GlobalTheory.HSApp.wtBig_run_alt)
    (Closed.and (Closed.and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz) (_root_.GlobalTheory.T.size_bounds_for_family_alt hSz)) hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨⟨_, -, a₃⟩, _, -, a₄⟩, _, -, a₅⟩
  obtain ⟨x0, a⟩ := (a₁.and a₂).and ((a₃.and a₄).and a₅)
  clear a₁ a₂ a₃ a₄ a₅
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩, a₅⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨hp1, hq1, hE, hQuo, hAnti, -, -⟩ := a₃ i hi
  obtain ⟨hLaw, hIn, -⟩ := a₄ i hi Y hY
  obtain ⟨-, -, -, -, -, -, ⟨Z'⟩, -⟩ := a₅ i hi Y hY
  have hW := a₂ i hi
  have hV := a₁ i hi Y hY
  rw [hQuo u1 hu1]
  have hPr := _root_.GlobalTheory.T.proportionality_principle_compactification h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hEq := _root_.GlobalTheory.T.compactification_top_chern_eq_volume h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hBir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hS hP h2.q15 h2.q16 _ p.T hLaw _ hp1 hq1 Y _ _ hY.1 _ (fun τ a b hab => by
    have hb := b.2
    have h := hW.gaps τ a (by rw [← hab]; exact hb)
    rw [gap_eq _ hab] at h
    refine le_trans ?_ h
    have e : ∀ d C N : ℕ, (d + 3) ^ 2 + 2 * N ≤ (d + 3) * (C + 4 * N + d + 3) := fun d C N => by nlinarith
    rw [GlobalTheory.CompHS.dimFlag_eq]
    exact_mod_cast e _ _ _)
  have key := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf hPr.1 hEq _ (fun τ => (hAnti τ).1) (fun τ => (hAnti τ).2) hBir hV
  refine ⟨CompHt.delPrime Y.U Z' _, ?_, fun Z => key Z Z'⟩
  exact mul_pos (hPr.2 Z') (Int.cast_pos.2 (CompHt.vdm_pos fun τ => (hAnti τ).2))
end GlobalTheory.CovTop.DegProof
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
theorem _root_.GlobalTheory.T.coverDegree_of_grothendieck_deformation : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree := by
  first | exact @_root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt | exact _root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt | (intros; apply _root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt <;> assumption)
end
end
