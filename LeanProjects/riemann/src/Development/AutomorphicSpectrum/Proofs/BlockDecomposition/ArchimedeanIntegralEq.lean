import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulticonePointDescendsToSubvarietyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypersurfaceComplexPointsMeasurableNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointsSecondCountableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyGenericallyEtaleCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFormNonvanishingOnChartStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionRegularOnNonvanishingChartStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BadProjectionLocusNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrregularProjectionImageNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalChartSheetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionLogNormOnSheetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityChartIntegralFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIntegralProjectionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetDensityLogNormFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernPartNullSetZeroStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section
namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

theorem ae_cover {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1)) (Ψ : LinProj n D)
    (hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ) (N : Pol n) (a : Fin (m + 1) → ℕ) (hN : IsMultiHomog N a)
    (hNP : N ∉ ptIdeal (i (genericPoint X)))
    (hcov : ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source) :
    ∀ᵐ v : Fin D → ℂ, ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
      ∃ y, Over i y z ∧ y ∈ pieceSet i Ψ N := by
  classical
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D => c.e.source) (fun c => c.e.open_source)
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.projB_null (J := Ideal.span {N}) Ψ hP hΨ
    ⟨{N}, by rintro f rfl; exact ⟨a, hN⟩, rfl⟩ (fun h => hNP (h (Ideal.subset_span rfl)))
  have h2 : volume (⋃ c ∈ T, projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y}) = 0 :=
    (measure_biUnion_null_iff hTc).2 fun c _ => GlobalTheory.T.irregular_projection_image_null m n X i D Ψ c
  have h3 := measure_union_null h1 h2
  refine ae_iff.2 (measure_mono_null ?_ h3)
  intro v hv
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨z, hz, hzv, hno⟩ := hv
  by_cases hNz : eval z (map (Int.castRingHom ℂ) N) = 0
  · refine Or.inl ⟨z, hz, ⟨hz.1, fun g hg => ?_⟩, hzv⟩
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    simp [hNz]
  · obtain ⟨y, hy⟩ := GlobalTheory.T.multicone_point_descends_to_subvariety m n X i z hz
    obtain ⟨c₀, hc₀⟩ := hcov y z hy hNz
    have hyU : y ∈ ⋃ c ∈ T, c.e.source := by
      rw [hTU]
      exact Set.mem_iUnion.2 ⟨c₀, hc₀⟩
    obtain ⟨c, hcT, hyc⟩ := Set.mem_iUnion₂.1 hyU
    have h0 : Ψ (segre z) 0 ≠ 0 := by simp [hzv]
    by_cases hreg : IsRegAt i Ψ c y
    · exact absurd ⟨y, hy, GlobalTheory.T.projection_regular_on_nonvanishing_chart m n X i D Ψ N a hN c y z hyc hy hNz h0 hreg⟩ hno
    · refine Or.inr (Set.mem_iUnion₂.2 ⟨c, hcT, y, ⟨hyc, ⟨z, hy, h0⟩, hreg⟩, ?_⟩)
      have hl : Over i y (liftOf i y) := by
        have hex : ∃ z, Over i y z := ⟨z, hy⟩
        simp only [liftOf, dif_pos hex]
        exact hex.choose_spec
      have ho : SameOrbit (liftOf i y) z := (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i y y _ _ hl hy).1 rfl
      rw [projCoord, ratios_eq_of_sameOrbit Ψ ho h0, ratios_of_proj Ψ hzv]

theorem exists_form_chart {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (hX : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D) :
    ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧ j ∉ ptIdeal (i (genericPoint X)) ∧
      ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 →
        ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source := by
  obtain ⟨U, x, hU, hg, hx⟩ := GlobalTheory.T.arithmetic_variety_generically_etale_coordinates X (i ≫ mpStr ℤ m n) D hX
  obtain ⟨j, a, hj, hjP, hjU⟩ := GlobalTheory.T.exists_form_nonvanishing_on_chart m n X i U hg
  refine ⟨j, a, hj, hjP, fun y z hyz hz => ?_⟩
  obtain ⟨c, hc, -⟩ := GlobalTheory.AlgChart.exists_of_etale hU x hx (hjU y z hyz hz)
  exact ⟨c, hc⟩

end GlobalTheory.CompanionTheory.MixZ.ArchEq

namespace GlobalTheory.CompanionTheory.MixZ

open ArchEq in

theorem archIntEq_of_integrable : ArchIntegrableOn → ArchIntEq := by
  intro hI m n Nh M B A hB hA X _ i _ D hX sB sA r hr f g hfg hrat
  classical
  have hC := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := GlobalTheory.T.mixed_cycle_point_dictionary m n X i (D + 1) hX.dim_eq
  have hP := hp₄ (hp₃.2 hC)
  have hPp : (ptIdeal (i (genericPoint X))).IsPrime := hP.2.1.1
  have hex : ∃ Ψ : LinProj n D, IsGoodProj (ptIdeal (i (genericPoint X))) Ψ :=
    ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists _ _ _ D hP
  haveI hsc : SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := GlobalTheory.T.complex_points_second_countable m n X i D hX
  unfold ptsIntegral
  rw [dif_pos hex]
  set Ψ : LinProj n D := hex.choose with hΨdef
  have hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ := hex.choose_spec
  obtain ⟨j, aj, hj, hjP, hjc⟩ := exists_form_chart i hX
  have hfg' := hfg
  obtain ⟨α, β, hα, hβ, hfP, hgP, -⟩ := hfg'
  set N : Pol n := j * f * g with hNdef
  have hNh : IsMultiHomog N (aj + α + β) := homog_mul (homog_mul hj hα) hβ
  have hNP : N ∉ ptIdeal (i (genericPoint X)) := fun h => by
    rcases hPp.mem_or_mem h with h | h
    · rcases hPp.mem_or_mem h with h | h
      · exact hjP h
      · exact hfP h
    · exact hgP h
  have hNe : ∀ z : (Σ k, Bk n k) → ℂ, eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      eval z (map (Int.castRingHom ℂ) j) ≠ 0 ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0 ∧
        eval z (map (Int.castRingHom ℂ) g) ≠ 0 := fun z h => by
    simp only [hNdef, map_mul, mul_ne_zero_iff] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hcov : ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source := fun y z h h' => hjc y z h (hNe z h').1

  have hL : (Nh.restr i).archInt (M.restr i) D hr =
      ((Nh.restr i).φ σ₀).chernInt D (offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr))
        (GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r) :=
    finsum_eq_single _ σ₀ fun σ hσ => absurd (Subsingleton.elim σ σ₀) hσ
  rw [hL]
  set S₀ := offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) with hS₀
  set F := GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r with hF
  set μ : ℤˣ → Measure (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := fun ε => ((Nh.restr i).φ σ₀).chernPart D ε with hμ
  set G := pieceSet i Ψ N with hG
  have hGo : IsOpen G := isOpen_pieceSet i Ψ N
  have hGS : G ⊆ S₀ := by
    rintro y ⟨e, Γ, hp, hy⟩
    have hv := hp.2.2 (e y) (e.map_source hy)
    rw [e.left_inv hy] at hv
    exact (GlobalTheory.T.rational_section_log_norm_on_sheet m n M A X i r hr f g hfg hrat y _ hv.1 (hNe _ hv.2.2.2).2.1 (hNe _ hv.2.2.2).2.2).1
  have hnull : ∀ ε, μ ε Gᶜ = 0 := fun ε => by
    refine GlobalTheory.T.chern_part_null_set_zero _ ε _ hGo.measurableSet.compl fun c => ?_
    have hsub : c.e.target ∩ c.e.symm ⁻¹' Gᶜ ⊆
        (c.e.target ∩ c.e.symm ⁻¹' {y | (∃ z, Over i y z ∧ Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) 0 = 0) ∨ ¬ IsRegAt i Ψ c y}) ∪
        (c.e.target ∩ c.e.symm ⁻¹' {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) N) = 0}) := by
      rintro v ⟨hv, hvG⟩
      obtain ⟨z, -, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i (c.e.symm v)
      by_cases hNz : eval z (map (Int.castRingHom ℂ) N) = 0
      · exact Or.inr ⟨hv, z, hz, hNz⟩
      · refine Or.inl ⟨hv, ?_⟩
        by_cases h0 : Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) 0 = 0
        · exact Or.inl ⟨z, hz, h0⟩
        · exact Or.inr fun hreg => hvG (GlobalTheory.T.projection_regular_on_nonvanishing_chart m n X i D Ψ N _ hNh c _ z (c.e.map_target hv) hz hNz h0 hreg)
    exact measure_mono_null hsub (measure_union_null (GlobalTheory.T.bad_projection_locus_null m n X i D hX Ψ hΨ c)
      ((GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D N _ hNh hNP).2 c))

  let J := {p : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ) ×
    ((Fin D → ℂ) → (Σ k, Bk n k) → ℂ) // IsPiece i Ψ N p.1 p.2}
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun p : J => p.1.1.source)
    (fun p => p.1.1.open_source)
  haveI : Countable T := hTc.to_subtype
  let e : T → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ) := fun l => l.1.1.1
  let Γ : T → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ := fun l => l.1.1.2
  have hpc : ∀ l, IsPiece i Ψ N (e l) (Γ l) := fun l => l.1.2
  let ρ : T → (Fin D → ℂ) → ℝ := fun l => maDensity (fun _ y' => Real.log (B.h (Γ l y')))
  have hd := fun l => GlobalTheory.T.local_chart_sheet_decomposition m n Nh B hB sB X i D Ψ N (e l) (Γ l) (hpc l)
  have hcovG : G ⊆ ⋃ l, (e l).source := by
    rintro y ⟨e', Γ', hp, hy⟩
    have hmem : y ∈ ⋃ p : J, p.1.1.source := Set.mem_iUnion.2 ⟨⟨(e', Γ'), hp⟩, hy⟩
    rw [← hTU] at hmem
    obtain ⟨p, hp, hy⟩ := Set.mem_iUnion₂.1 hmem
    exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, hy⟩
  have hIS := hI m n Nh M X i D hX r hr σ₀
  have hIG : ∀ ε, IntegrableOn F G (μ ε) := fun ε => by
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact hIS.1.mono_set hGS
    · exact hIS.2.mono_set hGS
  obtain ⟨S, hSm, hSs, hSd, hSU, hSI⟩ := GlobalTheory.T.density_chart_integral_formula μ e ρ (fun l => (hd l).1) (fun l ε => (hd l).2 ε) G
    hGo.measurableSet hcovG F hIG
  have hae : ∀ ε, S₀ =ᵐ[μ ε] G := fun ε => by
    refine (ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy.2) (hnull ε), ?_⟩)
    rw [Set.diff_eq_empty.2 hGS, measure_empty]
  have hchern : ((Nh.restr i).φ σ₀).chernInt D S₀ F = ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) := by
    rw [GlobalTheory.Weight.chernInt, setIntegral_congr_set (hae 1), setIntegral_congr_set (hae (-1))]
  rw [hchern, hSI, ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegralAt]
  refine integral_congr_ae ?_
  filter_upwards [ae_cover i hP Ψ hΨ N _ hNh hNP hcov, GlobalTheory.T.sheet_density_log_norm_formula m n _ D Ψ B A f g hP hΨ sB hfg] with v h1 h2
  have h3 : ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) = Fin.cons 1 v →
      ∃ y, Over i y z ∧ y ∈ ⋃ l, S l := fun z hz hzv => by
    rw [hSU]
    exact h1 z hz hzv
  have h4 := GlobalTheory.T.sheet_integral_projection_formula m n X i D Ψ N hP hΨ e Γ S hpc hSs hSd v h3
    (fun w => sheetDensity (ptIdeal (i (genericPoint X))) Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w)
    (fun l => F ((e l).symm v) * ρ l v) (fun l hl => by
      obtain ⟨y, hyS, rfl⟩ := hl
      have hvt := (e l).map_source (hSs l hyS)
      have hv := (hpc l).2.2 _ hvt
      have hs : IsSheet (ptIdeal (i (genericPoint X))) Ψ (e l y) (ReciprocityTheory.ChartRestriction.G.Geo.segre (Γ l (e l y))) (Γ l) := by
        refine ⟨rfl, ?_⟩
        filter_upwards [(e l).open_target.mem_nhds hvt] with v' hv'
        have hv2 := (hpc l).2.2 v' hv'
        exact ⟨(hpc l).2.1.differentiableAt ((e l).open_target.mem_nhds hv'), hv2.2.1, hv2.2.2.1⟩
      rw [h2 _ _ hs]
      congr 1
      exact (GlobalTheory.T.rational_section_log_norm_on_sheet m n M A X i r hr f g hfg hrat _ _ hv.1 (hNe _ hv.2.2.2).2.1 (hNe _ hv.2.2.2).2.2).2.symm)
  exact h4.symm

end GlobalTheory.CompanionTheory.MixZ
