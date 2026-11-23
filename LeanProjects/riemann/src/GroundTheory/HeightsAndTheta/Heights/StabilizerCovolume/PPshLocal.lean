import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExtB
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StPshLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real

noncomputable section

variable {D : ℕ} {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}

theorem PshLocal.usc
    (hloc : ∀ p ∈ U, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ) :
    UpperSemicontinuousOn φ U := by
  intro x hx y hy
  obtain ⟨W, hWo, hxW, -, hW⟩ := hloc x hx
  have h := hW.1 x hxW y hy
  rw [hWo.nhdsWithin_eq hxW] at h
  exact nhdsWithin_le_nhds h

theorem PshLocal.isPsh_max {W : Set (Fin D → ℂ)} (h : IsPsh W φ) (a : ℝ) :
    IsPsh W (fun x => max (φ x) a) := by
  refine ⟨h.1.sup upperSemicontinuousOn_const, fun z w hd => ?_⟩
  obtain ⟨hi, hm⟩ := h.2 z w hd
  have hca : CircleIntegrable (fun _ : ℂ => a) 0 1 := intervalIntegrable_const
  have hi' : CircleIntegrable (fun ζ : ℂ => max (φ (z + ζ • w)) a) 0 1 :=
    ⟨hi.1.sup hca.1, hi.2.sup hca.2⟩
  refine ⟨hi', max_le ?_ ?_⟩
  · exact hm.trans (circleAverage_mono hi hi' fun x _ => le_max_left _ _)
  · calc a = circleAverage (fun _ : ℂ => a) 0 1 := (circleAverage_const a 0 1).symm
      _ ≤ _ := circleAverage_mono hca hi' fun x _ => le_max_right _ _

theorem PshLocal.core (hU : IsOpen U)
    (hloc : ∀ p ∈ U, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ)
    (z w : Fin D → ℂ) (hD : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) {c : ℝ}
    (hc : ∀ θ : ℝ, c ≤ φ (z + circleMap 0 1 θ • w)) :
    IntervalIntegrable (fun θ => φ (z + circleMap 0 1 θ • w)) volume 0 (2 * π) ∧
      φ z ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, φ (z + circleMap 0 1 θ • w) := by
  have husc := PshLocal.usc hloc
  set K := (fun ζ : ℂ => z + ζ • w) '' closedBall (0 : ℂ) 1 with hKdef
  have hKc : IsCompact K := (isCompact_closedBall _ _).image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hD ζ (mem_closedBall_zero_iff.1 hζ)
  have hγ : Continuous (fun θ : ℝ => z + circleMap 0 1 θ • w) :=
    continuous_const.add ((continuous_circleMap 0 1).smul continuous_const)
  have hcirc : ∀ θ : ℝ, z + circleMap 0 1 θ • w ∈ K := fun θ =>
    ⟨circleMap 0 1 θ, mem_closedBall_zero_iff.2 (by simp), rfl⟩
  have hzK : z ∈ K := ⟨0, mem_closedBall_self zero_le_one, by simp⟩
  choose W hWo hpW hWU hWpsh using hloc
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric hKc (c := fun p : U => W p.1 p.2)
    (fun p => hWo _ _) (fun x hx => mem_iUnion.2 ⟨⟨x, hKU hx⟩, hpW _ _⟩)
  obtain ⟨δ', hδ', hδ'U⟩ := hKc.exists_cthickening_subset_open hU hKU
  obtain ⟨M, hM⟩ := (husc.mono hδ'U).bddAbove_of_isCompact hKc.cthickening
  have hMK : ∀ y ∈ cthickening δ' K, φ y ≤ M := fun y hy => hM ⟨y, hy, rfl⟩
  obtain ⟨ρ⟩ := mollifierInhabit_thm D
  have hε0 : 0 < min (δ / 2) δ' := lt_min (by linarith) hδ'
  have step : ∀ ε, 0 < ε → ε < min (δ / 2) δ' →
      (∀ x ∈ K, φ x ≤ molli ρ ε φ x ∧ molli ρ ε φ x ≤ M) ∧
      Continuous (fun θ : ℝ => molli ρ ε φ (z + circleMap 0 1 θ • w)) ∧
      molli ρ ε φ z ≤ circleAverage (fun ζ : ℂ => molli ρ ε φ (z + ζ • w)) 0 1 := by
    intro ε hε hεlt
    have hεδ : ε < δ := by have := min_le_left (δ / 2) δ'; linarith
    have hεδ' : ε ≤ δ' := by have := min_le_right (δ / 2) δ'; linarith
    have hm := fun p : U => (mollify_thm D ρ (W p.1 p.2) φ (hWo _ _) (hWpsh _ _)).1 ε hε
    have hm2 : ∀ p : U, ContDiffOn ℝ 2 (molli ρ ε φ) (shrink (W p.1 p.2) ε) := fun p =>
      (hm p).2.1.of_le (WithTop.coe_le_coe.2 le_top)
    set V := ⋃ p : U, shrink (W p.1 p.2) ε with hV
    have hVo : IsOpen V := isOpen_iUnion fun p => (hm p).1
    have hKV : ∀ x ∈ K, ∃ p : U, x ∈ shrink (W p.1 p.2) ε := by
      intro x hx
      obtain ⟨p, hp⟩ := hδK x hx
      exact ⟨p, (closedBall_subset_ball hεδ).trans hp⟩
    have hcd : ContDiffOn ℝ 2 (molli ρ ε φ) V := by
      refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
      obtain ⟨p, hp⟩ := mem_iUnion.1 hy
      exact ⟨_, (hm p).1, hp, (hm2 p).mono inter_subset_right⟩
    have hpsh : IsPsh V (molli ρ ε φ) := by
      refine (isPsh_iff_isLeviPsh_thm D V _ hVo hcd).2 ⟨hcd, fun y hy v => ?_⟩
      obtain ⟨p, hp⟩ := mem_iUnion.1 hy
      exact ((isPsh_iff_isLeviPsh_thm D _ _ (hm p).1 (hm2 p)).1 (hm p).2.2.1).2 y hp v
    have hmemV : ∀ x ∈ K, x ∈ V := fun x hx =>
      let ⟨p, hp⟩ := hKV x hx
      mem_iUnion.2 ⟨p, hp⟩
    refine ⟨fun x hx => ?_, hcd.continuousOn.comp_continuous hγ fun θ => hmemV _ (hcirc θ),
      (hpsh.2 z w fun ζ hζ => hmemV _ ⟨ζ, mem_closedBall_zero_iff.2 hζ, rfl⟩).2⟩
    obtain ⟨p, hp⟩ := hKV x hx
    obtain ⟨h1, h2⟩ := (hm p).2.2.2 x hp
    refine ⟨h1, h2.trans (polyMax_le' hε.le fun y hy => hMK y ?_)⟩
    exact cthickening_mono hεδ' K (closedBall_subset_cthickening hx ε hy)
  set f : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w) with hf
  set B := max |c| |M|
  have hbd : ∀ t : ℝ, c ≤ t → t ≤ M → |t| ≤ B := fun t h1 h2 => by
    rw [abs_le]
    constructor
    · have := neg_abs_le c
      have := le_max_left |c| |M|
      linarith
    · have := le_abs_self M
      have := le_max_right |c| |M|
      linarith
  have hfM : ∀ θ, f θ ≤ M := fun θ => hMK _ (self_subset_cthickening K (hcirc θ))
  have hfm : Measurable f :=
    (upperSemicontinuousOn_univ_iff.1
      (husc.comp hγ.continuousOn fun θ _ => hKU (hcirc θ))).measurable
  refine ⟨PlurisubharmonicExtension.ii_of_bdd hfm B (fun θ => hbd _ (hc θ) (hfM θ)) _ _, ?_⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < min (δ / 2) δ' := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε0)] with ε h1 h2
    exact ⟨h1, h2⟩
  have hT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * π) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε θ => molli ρ ε φ (z + circleMap 0 1 θ • w)) (f := f) (fun _ => B)
    (hev.mono fun ε h => (step ε h.1 h.2).2.1.aestronglyMeasurable)
    (hev.mono fun ε h => ae_of_all _ fun θ _ => by
      obtain ⟨h1, h2⟩ := (step ε h.1 h.2).1 _ (hcirc θ)
      rw [Real.norm_eq_abs]
      exact hbd _ ((hc θ).trans h1) h2)
    intervalIntegrable_const
    (ae_of_all _ fun θ _ =>
      (mollify_thm D ρ _ φ (hWo _ (hKU (hcirc θ))) (hWpsh _ _)).2 _ (hpW _ _))
  refine ge_of_tendsto (hT.const_mul (2 * π)⁻¹) (hev.mono fun ε h => ?_)
  obtain ⟨h1, -, h3⟩ := step ε h.1 h.2
  rw [circleAverage_def, smul_eq_mul] at h3
  exact (h1 z hzK).1.trans h3

theorem PshLocal.proof : PshLocal.Statement := by
  intro D U φ hU hloc
  refine ⟨PshLocal.usc hloc, fun z w hD => ?_⟩
  set f : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w) with hf
  set g : ℕ → ℝ → ℝ := fun n θ => max (f θ) (-(n : ℝ)) with hg
  have hcore : ∀ n : ℕ, IntervalIntegrable (g n) volume 0 (2 * π) ∧
      φ z ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, g n θ := fun n => by
    have := PshLocal.core (φ := fun x => max (φ x) (-(n : ℝ))) hU
      (fun p hp => let ⟨W, h1, h2, h3, h4⟩ := hloc p hp; ⟨W, h1, h2, h3, PshLocal.isPsh_max h4 _⟩)
      z w hD (c := -(n : ℝ)) (fun θ => le_max_right _ _)
    exact ⟨this.1, (le_max_left _ _).trans this.2⟩
  have hγ : Continuous (fun θ : ℝ => z + circleMap 0 1 θ • w) :=
    continuous_const.add ((continuous_circleMap 0 1).smul continuous_const)
  set S := (fun ζ : ℂ => z + ζ • w) '' sphere (0 : ℂ) 1 with hSdef
  have hSc : IsCompact S := (isCompact_sphere _ _).image (by fun_prop)
  have hSU : S ⊆ U := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hD ζ (mem_sphere_zero_iff_norm.1 hζ).le
  have hcS : ∀ θ : ℝ, z + circleMap 0 1 θ • w ∈ S := fun θ =>
    ⟨_, circleMap_mem_sphere 0 zero_le_one θ, rfl⟩
  obtain ⟨M, hM⟩ := ((PshLocal.usc hloc).mono hSU).bddAbove_of_isCompact hSc
  have hfM : ∀ θ, f θ ≤ M := fun θ => hM ⟨_, hcS θ, rfl⟩
  set μ := volume.restrict (Ioc (0 : ℝ) (2 * π)) with hμ
  have hgi : ∀ n, Integrable (g n) μ := fun n =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 (hcore n).1
  have hgl : ∀ θ, Tendsto (fun n => g n θ) atTop (𝓝 (f θ)) := by
    intro θ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈-f θ⌉₊] with n hn
    have h1 := Nat.le_ceil (-f θ)
    have h2 : ((⌈-f θ⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    exact (max_eq_left (by linarith)).symm
  have hlow : ∀ n, 2 * π * φ z ≤ ∫ θ, g n θ ∂μ := fun n => by
    rw [hμ, ← intervalIntegral.integral_of_le two_pi_pos.le]
    exact (le_inv_mul_iff₀ two_pi_pos).1 (hcore n).2
  set P := max M 0 with hP
  have hnorm : ∀ n, ∫ θ, ‖g n θ‖ ∂μ ≤ 2 * P * (2 * π) - 2 * π * φ z := fun n => by
    have hle : ∀ θ, ‖g n θ‖ ≤ 2 * P - g n θ := fun θ => by
      have h1 : g n θ ≤ P := max_le ((hfM θ).trans (le_max_left _ _))
        ((neg_nonpos.2 (Nat.cast_nonneg n)).trans (le_max_right _ _))
      have h2 : 0 ≤ P := le_max_right _ _
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hμu : μ.real univ = 2 * π := by
      simp [hμ, Real.volume_real_Ioc, two_pi_pos.le]
    calc ∫ θ, ‖g n θ‖ ∂μ ≤ ∫ θ, (2 * P - g n θ) ∂μ :=
          integral_mono (hgi n).norm ((integrable_const _).sub (hgi n)) hle
      _ = 2 * P * (2 * π) - ∫ θ, g n θ ∂μ := by
          rw [integral_sub (integrable_const _) (hgi n), integral_const, hμu, smul_eq_mul, mul_comm]
      _ ≤ _ := by linarith [hlow n]
  have hfi : Integrable f μ := by
    refine integrable_of_tendsto (G := g) (ae_of_all _ hgl)
      (fun n => (hgi n).aestronglyMeasurable) ?_
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * P * (2 * π) - 2 * π * φ z))
      (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hgi n)]
    exact ENNReal.ofReal_le_ofReal (hnorm n)
  have hT := integral_tendsto_of_tendsto_of_antitone hgi hfi
    (ae_of_all _ fun θ n m hnm => max_le_max le_rfl (neg_le_neg (Nat.cast_le.2 hnm)))
    (ae_of_all _ hgl)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).2 hfi, ?_⟩
  rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le]
  exact (le_inv_mul_iff₀ two_pi_pos).2 (ge_of_tendsto' hT fun n => hlow n)

end

end GroundTheory.Heights₂.Heights.NineStatements
