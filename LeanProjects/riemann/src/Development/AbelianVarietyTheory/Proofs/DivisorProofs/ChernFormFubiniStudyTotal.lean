import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianDeterminantRealPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartComplementDenseOpenNullFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.FSMass

theorem chern_mass_hermitian_O_one_projective : ∀ N : ℕ, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N 1 Set.univ = 1 ∧ ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N (-1) Set.univ = 0 := by
  intro N
  have hproj : IsProjOver (PSpace.str ℂ N) := ProjSpace.isProjOver_str ℂ N
  haveI : IsIntegral (PSpace ℂ N) := ProjSpace.isIntegral_of_isDomain ℂ N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).IsCInf := (ProjSpace.hermitianTwistingSheaf ℂ N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf ℂ N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := GlobalTheory.T.exists_projSpace_standardChart_fubiniStudy N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace ℂ N) ∈ ProjSpace.chart ℂ N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace ℂ N)).mem_open_set_iff (ProjSpace.chart ℂ N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := GlobalTheory.T.chernPart_complement_dense_open_null_field ℂ (PSpace ℂ N) (PSpace.str ℂ N) (RingHom.id ℂ) N hproj _ hgen _
    ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)) 1
  rw [← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (GlobalTheory.T.lintegral_fubiniStudy_density_eq_one' N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, GlobalTheory.T.det_complexHessian_fubiniStudy_potential N v]
  simp
end GlobalTheory.FSMass
