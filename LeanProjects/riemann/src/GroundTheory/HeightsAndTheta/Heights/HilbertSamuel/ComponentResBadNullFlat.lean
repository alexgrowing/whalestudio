import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ComponentResBadNullLift
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeK
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem isAnalyticSubset_D :
    R.atlas.IsAnalyticSubset {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} := by
  intro x
  set i := R.idx x
  obtain ⟨n, g, hg⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family).mp (IsNoetherian.noetherian (R.R.bd i))
  refine ⟨R.R.src i, R.R.isOpen_alt_bis i, R.mem_src_idx x, n, fun l y => eval (R.R.coord i y) (g l),
    fun l => R.isGoodAtlas.1 i (g l), ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyD, hy⟩
    refine ⟨hy, fun l => ?_⟩
    have hz := (R.R.zero_bd i y hy).mpr ((pt_mem_D_iff R hy).mp hyD)
    have hgl : g l ∈ R.R.bd i := by
      rw [← hg]
      exact Submodule.subset_span ⟨l, rfl⟩
    exact hz _ hgl
  · rintro ⟨hy, hz⟩
    refine ⟨(pt_mem_D_iff R hy).mpr ((R.R.zero_bd i y hy).mp fun h hh => ?_), hy⟩
    rw [← hg] at hh
    induction hh using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl⟩ := ha
      exact hz l
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [smul_eq_mul, hb]

theorem interior_D : interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  set i := R.idx x
  have hxi : x ∈ R.R.src i := R.mem_src_idx x
  set sd := R.R.sncAt i x hxi
  have hcont : ContinuousOn (fun y => eval (R.R.coord i y) sd.h) (R.R.src i) :=
    (MvPolynomial.continuous_eval sd.h).comp_continuousOn
      (continuousOn_iff_continuous_domRestrict.mpr (R.R.isEmbedding i).continuous)
  set O := interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} ∩
    (R.R.src i ∩ (fun y => eval (R.R.coord i y) sd.h) ⁻¹' {0}ᶜ) with hOdef
  have hO : IsOpen O :=
    isOpen_interior.inter (hcont.isOpen_inter_preimage (R.R.isOpen_alt_bis i) isOpen_compl_singleton)
  have hxO : x ∈ O := ⟨hx, hxi, sd.eval_h⟩
  obtain ⟨ψ, -, hxψ, hsub, hform⟩ := R.isGoodAtlas.2 i x hxi sd.r sd.span_eq O hO hxO
  have hnull : volume ψ.target = 0 := by
    refine measure_mono_null (t := ⋃ l : Fin e, {u : Fin e → ℂ | u l = 0}) ?_
      (measure_iUnion_null fun l => ?_)
    · intro u hu
      have hy : ψ.symm u ∈ ψ.source := ψ.map_target hu
      have hyO := hsub hy
      have hyD : R.pt (ψ.symm u) ∈ ReciprocityTheory.AnForm.R.conePts R.D :=
        (interior_subset (s := {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) hyO.1.1 :)
      have hbd := (R.R.zero_bd i (ψ.symm u) hyO.2).mpr ((pt_mem_D_iff R (x := x) hyO.2).mp hyD)
      have h0 := hbd _ sd.mem_bd
      rw [map_mul, map_prod] at h0
      have hprod := (mul_eq_zero.mp h0).resolve_left hyO.1.2.2
      obtain ⟨l, -, hl0⟩ := Finset.prod_eq_zero_iff.mp hprod
      have hu' : u = ReciprocityTheory.AnForm.R.evalFam sd.r (R.R.coord i (ψ.symm u)) :=
        (ψ.right_inv hu).symm.trans (hform _ hy)
      exact Set.mem_iUnion.mpr ⟨l, (congrFun hu' l).trans hl0⟩
    · rw [MeasureTheory.volume_pi]
      exact Measure.pi_hyperplane _ l 0
  exact (ψ.open_target.measure_pos volume ⟨ψ x, ψ.map_source hxψ⟩).ne' hnull

theorem D_null (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) = 0 := by
  refine measure_mono_null ?_
    (ReciprocityTheory.AnForm.M.analyticNull R.atlas _ (isAnalyticSubset_D R) (interior_D R) j)
  rintro u ⟨hu, hD⟩
  exact ⟨(R.atlas.chart j).symm u, ⟨hD, (R.atlas.chart j).map_target hu⟩, (R.atlas.chart j).right_inv hu⟩

theorem isOpen_chart_notD (j : Fin R.atlas.n) :
    IsOpen ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, hB1⟩
  set x1 := (R.atlas.chart j).symm u1
  have hV : (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x1) ∈ 𝓝 u1 :=
    ((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)).mem_nhds
      ⟨hu1, R.mem_src_idx x1⟩
  have hnot : ¬ ∀ f ∈ R.D, eval (R.liftAt x1 x1) f = 0 := fun h =>
    hB1 ⟨(GroundTheory.Heights₂.Heights.Inter.res_mem R x1 (R.mem_src_idx x1)).1, h⟩
  push Not at hnot
  obtain ⟨f, hfD, hf0⟩ := hnot
  have hcont : ContinuousAt (fun u => eval (R.liftAt x1 ((R.atlas.chart j).symm u)) f) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (R.analyticAt_liftAt_pi x1 j ⟨hu1, R.mem_src_idx x1⟩).continuousAt
  filter_upwards [hV, hcont.eventually_ne hf0] with u hu hne
  refine ⟨hu.1, fun hB => ?_⟩
  exact hne (((pt_mem_D_iff R hu.2).mp hB).2 f hfD)

theorem not_flat {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n)
    {O : Set (Fin e → ℂ)} (hO : IsOpen O) (hOt : O ⊆ (R.atlas.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (R.pt ((R.atlas.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by
  set O' := O ∩ ((R.atlas.chart j).target ∩
    (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D}) with hO'def
  have hO' : IsOpen O' := hO.inter (isOpen_chart_notD R j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨u, hu⟩ := hne
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u hu
    have hsub : Metric.ball u r ⊆ (R.atlas.chart j).target ∩
        (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} := by
      intro v hv
      have hvO := hball hv
      refine ⟨hOt hvO, ?_⟩
      by_contra hB
      have : v ∈ O' := ⟨hvO, hOt hvO, hB⟩
      rw [h] at this
      exact this
    exact (Metric.measure_ball_pos volume u hr).ne' (measure_mono_null hsub (D_null R j))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono inter_subset_left)
    (fun u hu => hdet u hu.1)
  refine (resFib_finite R hP hW Ψ hΨ y).not_infinite ((Set.Infinite.image
    ((R.atlas.chart j).symm.injOn.mono fun u hu => hOt hu.1.1) hy).mono ?_)
  rintro _ ⟨u, ⟨huO, hqu⟩, rfl⟩
  exact ⟨hqu, huO.2.2, h0 u huO.1⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
