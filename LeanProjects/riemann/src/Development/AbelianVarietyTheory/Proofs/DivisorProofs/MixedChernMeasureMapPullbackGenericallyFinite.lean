import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeComplexPointsProperClosedChartField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenComplexPointsCoveringGenericDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicChartsGenericPointProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityPullbackMatchingChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityChangeOfChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.Mix.map_part_pull_of_genFinite : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), Measure.map (ptMap π hπ σ) (part (fun i => (L i).pull π hπ) ε) = (π.residueDegree (genericPoint Y) : ENNReal) • part L ε := by
  intro F _ X Y _ _ p q σ D hp hD hq π hπ hgen hdeg L ε
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hq
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hq
  haveI : IsLocallyNoetherian X := by
    obtain ⟨N, i, _, rfl⟩ := hp
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str F N
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str F N)
  obtain ⟨U, hU, hfibU, hchU⟩ := GlobalTheory.T.exists_open_complexPoints_covering_generic_degree F X Y p q σ D hp hq π hπ hgen hdeg
  obtain ⟨U', hU', hcharts⟩ := GlobalTheory.T.exists_holomorphic_charts_genericPoint_projective F X p σ D hp hD
  set m := ptMap π hπ σ with hm_def
  set Z : Set X := ((U ⊓ U' : X.Opens) : Set X)ᶜ with hZ_def
  have hZ : IsClosed Z := (U ⊓ U').isOpen.isClosed_compl
  have hgZ : genericPoint X ∉ Z := fun h => h ⟨hU, hU'⟩
  set T : Set (CxPts p σ) := (ptsIn p σ (U ⊓ U'))ᶜ with hT_def
  have hTset : T = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    ext y
    simp only [hT_def, hZ_def, mem_compl_iff, mem_setOf_eq, mem_ptsIn]
    rfl
  have hmT : m ⁻¹' T = {z : CxPts q σ | z.1 (IsLocalRing.closedPoint ℂ) ∈ π ⁻¹' Z} := by
    rw [hTset]
    ext z
    simp only [mem_preimage, mem_setOf_eq, hm_def, ptMap, PtsOver.map_val]
    rfl
  have hZ' : IsClosed (π ⁻¹' Z : Set Y) := hZ.preimage π.continuous
  have hgZ' : genericPoint Y ∉ (π ⁻¹' Z : Set Y) := by
    simp only [mem_preimage, hgen]
    exact hgZ
  have hm : Continuous m := PtsOver.continuous_map π hπ (spMap σ)
  refine GlobalTheory.GlueCoverNull.map_glueMeas_of_cover D (CxPts p σ) (CxPts q σ) (AlgChart p σ D) (AlgChart q σ D)
    (fun c => c.e) (fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y))
    (fun c => c.e) (fun c y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y))
    (fun i j => i.holo_trans j) ?_ (fun i j => i.holo_trans j) ?_ m hm T
    (isOpen_ptsIn _).isClosed_compl ?_ ?_ _ ?_ ?_
  · intro i j y hi hj
    rw [GlobalTheory.T.mixedChernFormDensity_change_of_chart F X p σ D L i j y hi hj, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · intro i j y hi hj
    rw [GlobalTheory.T.mixedChernFormDensity_change_of_chart F Y q σ D _ i j y hi hj, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · intro c
    rw [hTset]
    exact GlobalTheory.ChernNull.chart_null_field F X p σ D Z hZ hgZ c
  · intro c
    rw [hmT]
    exact GlobalTheory.ChernNull.chart_null_field F Y q σ D _ hZ' hgZ' c
  · intro x hx
    have hx' : x ∈ ptsIn p σ (U ⊓ U') := not_not.1 hx
    exact hfibU x (mem_ptsIn_inf.1 hx').1
  · intro z hz
    have hz' := mem_ptsIn_inf.1 (not_not.1 hz : m z ∈ ptsIn p σ (U ⊓ U'))
    obtain ⟨c, hc⟩ := hcharts (m z) hz'.2
    obtain ⟨c', hzc', hw⟩ := hchU z hz'.1 c hc
    refine ⟨c, c', hzc', hc, fun w hwc' _ => ⟨(hw w hwc').2, ?_⟩⟩
    rw [GlobalTheory.T.mixedChernFormDensity_pullback_matching_charts F X Y p q σ D π hπ L c c' hw w hwc']
