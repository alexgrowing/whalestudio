import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackIsPotentialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionFiniteOpenCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogNormContinuousOffDivisorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulticonePointDescendsToSubvarietyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureZeroSetAvoidedByHolomorphicMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypersurfaceComplexPointsMeasurableNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightsIntegralPullbackFormulaStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.ArchI

theorem exists_modif (hK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0})
    [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ) (hX : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D) :
    ∃ (T : Type) (_ : TopologicalSpace T) (_ : CompactSpace T) (_ : T2Space T) (A : FinHolAtlas D T)
      (F : T → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Z : Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)),
      Continuous F ∧
      (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ F)) ∧
      MeasurableSet Z ∧ (∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) ∧
      (∀ y, y ∉ Z → ∃ x, F x = y) ∧ (∀ x x', F x ∉ Z → F x = F x' → x = x') := by
  have hC := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := GlobalTheory.T.mixed_cycle_point_dictionary m n X i (D + 1) hX.dim_eq
  have hP := hp₄ (hp₃.2 hC)
  obtain ⟨J, ⟨R⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.exists_anLogRes (GlobalTheory.T.resolution_exists_of_resolution_statement hK) hP
  obtain ⟨S, hS, hJ⟩ := R.homog
  obtain ⟨f, hfS, hfP⟩ : ∃ f ∈ S, f ∉ ptIdeal (i (genericPoint X)) := by
    by_contra h
    push_neg at h
    exact R.nondeg (hJ ▸ Ideal.span_le.2 h)
  obtain ⟨a, ha⟩ := hS f hfS
  have hfJ : f ∈ J := hJ ▸ Ideal.subset_span hfS
  have hJz : ∀ z ∈ mcPts J, eval z (map (Int.castRingHom ℂ) f) = 0 := fun z hz => hz.2 f hfJ
  choose F hF' using fun x => GlobalTheory.T.multicone_point_descends_to_subvariety m n X i (R.lift x x) (R.mem x x (R.mem_U x))
  have hU : ∀ x, ∀ y ∈ R.U x, IsUnder (PtsOver.map i rfl _ (F y)) (R.lift x y) := fun x y hy =>
    GlobalTheory.T.isUnder_of_same_orbit m n _ _ _ (hF' y) (R.compat x y y ⟨hy, R.mem_U y⟩)
  have key (x : R.X) (j : Fin R.A.n) := GlobalTheory.T.holomorphic_lift_gives_holomorphic_section m n X i D
    ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) (fun v => R.lift x ((R.A.chart j).symm v))
    (F ∘ (R.A.chart j).symm) ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x))
    (fun u hu => (ReciprocityTheory.ChartRestriction.G.Geo.analyticAt_lift_chart R x j hu).differentiableAt.differentiableWithinAt)
    (fun v hv => hU x _ hv.2)
  have hO (x : R.X) (j : Fin R.A.n) := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨j, hj⟩ := R.A.cover x
    have hm : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      ⟨(R.A.chart j).map_source hj, by
        simpa only [Set.mem_preimage, (R.A.chart j).left_inv hj] using R.mem_U x⟩
    have h₁ := ((key x j).1.continuousAt ((hO x j).mem_nhds hm)).comp
      (f := R.A.chart j) (x := x) ((R.A.chart j).continuousAt hj)
    refine h₁.congr ?_
    filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw
    simp only [Function.comp_apply, (R.A.chart j).left_inv hw]
  refine ⟨R.X, inferInstance, inferInstance, inferInstance, R.A, F,
    {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) f) = 0}, hFc, ?_,
    (GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D f a ha hfP).1, (GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D f a ha hfP).2, ?_, ?_⟩
  · intro W g j v hv
    set x := (R.A.chart j).symm v with hx
    have hvO : v ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x := ⟨hv.1, R.mem_U x⟩
    have hcont := (key x j).1
    have hO' : IsOpen (((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) ∩
        (F ∘ (R.A.chart j).symm) ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) :=
      hcont.isOpen_inter_preimage (hO x j) (isOpen_ptsIn W)
    have hd := (key x j).2 W g
    exact (SCV.analyticOnNhd_iff_differentiableOn hO').2 hd v ⟨hvO, hv.2⟩
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
    have hzJ : z ∉ mcPts J := fun h => hy ⟨z, hyz, hJz z h⟩
    obtain ⟨x, hx⟩ := R.surj z hz hzJ
    exact ⟨x, (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ (hF' x) hyz).2 hx⟩
  · intro x x' hx e
    refine R.inj x x' (fun h => hx ⟨_, hF' x, hJz _ h⟩) ?_
    exact (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ (hF' x) (hF' x')).1 e

theorem integrableOn_of_modif {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp ℤ} {σ : ℤ →+* ℂ} {D : ℕ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {T : Type} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F)
    (H : ∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F))
    (Z : Set (GlobalTheory.CxPts q σ)) (hZ : MeasurableSet Z)
    (hZ0 : ∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0)
    (hs : ∀ y, y ∉ Z → ∃ x, F x = y) (hi : ∀ x x', F x ∉ Z → F x = F x' → x = x')
    {B C : LB X} (φ : GlobalTheory.Weight q σ B) (hφ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (hψ : ψ.IsCInf)
    {r : C.ι → X.functionFieldˣ} (hr : IsRatSec C r) (ε : ℤˣ) :
    IntegrableOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) (φ.chernPart D ε) := by
  classical
  obtain ⟨N, W, b, a, d, hcov, hWb, hd, hf⟩ := GlobalTheory.T.rational_section_finite_open_cover ψ hr
  set S := offSupp q σ (divOfRatSec ψ.isLB hr) with hSdef
  have hSo : IsOpen S := isOpen_offSupp _
  have hgc := GlobalTheory.T.log_norm_continuous_off_divisor ψ hψ hr
  set g := GlobalTheory.Cartier.logNorm ψ r with hgdef
  set Z' : Set (GlobalTheory.CxPts q σ) := Z ∪ ⋃ l, {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} with hZ'def
  have hpiece (l : Fin N) : MeasurableSet {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} := by
    have ho : IsOpen (ptsIn q σ (W l) ∩ ev q σ (W l) (d l) ⁻¹' {0}ᶜ) :=
      (continuousOn_ev (d l)).isOpen_inter_preimage (isOpen_ptsIn _) isOpen_compl_singleton
    have e : {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} =
        ptsIn q σ (W l) \ (ptsIn q σ (W l) ∩ ev q σ (W l) (d l) ⁻¹' {0}ᶜ) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, not_and, not_not]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
    rw [e]
    exact (isOpen_ptsIn _).measurableSet.diff ho.measurableSet
  have hZ'm : MeasurableSet Z' := hZ.union (MeasurableSet.iUnion hpiece)
  have hZ'0 : ∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z') = 0 := fun c => by
    rw [hZ'def, Set.preimage_union, Set.inter_union_distrib_left, Set.preimage_iUnion, Set.inter_iUnion]
    refine measure_union_null (hZ0 c) (measure_iUnion_null fun l => ?_)
    obtain ⟨h, hne⟩ := hd l
    exact GlobalTheory.T.zero_locus_regular_function_null X q σ D c (W l) h (d l) hne
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set Pt := hne.some
  have hKK (j : Fin A.n) := image_closed_compact (A.chart j) (isClosed_tsupport (Pt.χ j)) (Pt.tsupport_subset j)
  have hcovK : ∀ x, ∃ j, ∃ u ∈ (A.chart j) '' tsupport (Pt.χ j), (A.chart j).symm u = x := fun x => by
    obtain ⟨j, hj⟩ : ∃ j, Pt.χ j x ≠ 0 := by
      by_contra h
      push_neg at h
      have := Pt.sum_eq_one x
      simp [h] at this
    have hx : x ∈ tsupport (Pt.χ j) := subset_tsupport _ hj
    exact ⟨j, _, ⟨x, hx, rfl⟩, (A.chart j).left_inv (Pt.tsupport_subset j hx)⟩
  have hle := GlobalTheory.T.measure_zero_set_avoided_by_holomorphic_map A F hF H Z' hZ'm hZ'0 (fun y hy => hs y fun h => hy (Or.inl h))
    (fun x x' hx => hi x x' fun h => hx (Or.inl h)) φ hφ ε (fun j => (A.chart j) '' tsupport (Pt.χ j))
    (fun j => (hKK j).1) (fun j => (hKK j).2) hcovK
  have hfin (j : Fin A.n) := GlobalTheory.T.lintegral_indicator_mul_locDens_pullback_lt_top A F hF H φ hφ ψ hψ g S Z' W b a d hcov hWb
    (fun l y hy hyS hyZ => hf l y hy hyS fun h0 => hyZ (Or.inr (Set.mem_iUnion.2 ⟨l, hy, h0⟩))) hSo hgc hZ'm j
    _ (hKK j).2 (hKK j).1
  refine ⟨hgc.aestronglyMeasurable hSo.measurableSet, ?_⟩
  set h : GlobalTheory.CxPts q σ → ENNReal := S.indicator fun y => ‖g y‖ₑ with hh
  have hhm : Measurable h := by
    have := (hgc.enorm).measurable_piecewise (continuousOn_const (c := (0 : ENNReal)) (s := Sᶜ)) hSo.measurableSet
    rwa [show S.piecewise (fun y => ‖g y‖ₑ) (fun _ => (0 : ENNReal)) = h from Set.piecewise_eq_indicator] at this
  show ∫⁻ y, ‖g y‖ₑ ∂(φ.chernPart D ε).restrict S < ⊤
  rw [← lintegral_indicator hSo.measurableSet]
  refine (lintegral_mono' hle le_rfl).trans_lt ?_
  rw [lintegral_finset_sum_measure]
  refine ENNReal.sum_lt_top.2 fun j _ => ?_
  have hT := (A.chart j).open_target.measurableSet
  have hc : ContinuousOn (F ∘ (A.chart j).symm) (A.chart j).target :=
    hF.comp_continuousOn (A.chart j).continuousOn_symm
  have hsub : (A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z' ⊆ (A.chart j).target :=
    Set.diff_subset.trans (hKK j).2
  have hm₀ : AEMeasurable (F ∘ (A.chart j).symm)
      (volume.restrict ((A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z')) :=
    (hc.aemeasurable hT).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hdc := locDensCont A (fun _ => φ.locPot.pullback F hF)
    (fun _ => GlobalTheory.T.smooth_weight_pullback_is_potential A F hF H φ hφ) j
  have hρ : AEMeasurable (fun u => ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|)
      (volume.restrict ((A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z')) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn hdc.abs).aemeasurable hT).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  rw [lintegral_map' hhm.aemeasurable (hm₀.mono_ac (withDensity_absolutelyContinuous _ _))]
  change ∫⁻ u, (h ∘ F ∘ (A.chart j).symm) u ∂_ < ⊤
  rw [lintegral_withDensity_eq_lintegral_mul₀ hρ (hhm.comp_aemeasurable hm₀)]
  refine lt_of_eq_of_lt (lintegral_congr fun u => ?_) (hfin j)
  simp only [Pi.mul_apply, Function.comp_apply, hh]
  exact mul_comm _ _

end GlobalTheory.CompanionTheory.ArchI

namespace GlobalTheory.CompanionTheory.MixZ

open GlobalTheory.CompanionTheory.ArchI in

theorem archIntegrableOn_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ArchIntegrableOn := by
  intro hK m n N M X _ i _ D hX r hr σ
  obtain rfl : σ = σ₀ := Subsingleton.elim _ _
  obtain ⟨T, _, _, _, A, F, Z, hF, H, hZ, hZ0, hs, hi⟩ := exists_modif hK m n X i D hX
  have := hX.compactSpace σ₀
  exact ⟨integrableOn_of_modif A F hF H Z hZ hZ0 hs hi _ ((N.restr i).cInf σ₀) _ ((M.restr i).cInf σ₀) hr 1,
    integrableOn_of_modif A F hF H Z hZ hZ0 hs hi _ ((N.restr i).cInf σ₀) _ ((M.restr i).cInf σ₀) hr (-1)⟩

end GlobalTheory.CompanionTheory.MixZ
