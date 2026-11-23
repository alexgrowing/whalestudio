import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic

namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}

structure IsAlgebraicChart (e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜)) : Prop where
  exists_eq_div : ∃ (x : Fin d → A) (s : A), ∀ p ∈ e.source, p s ≠ 0 ∧ ∀ i, e p i = p (x i) / p s
  analyticOnNhd : ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target

variable (𝕜 A d) in

def HasAlgebraicCharts : Prop :=
  ∀ p : A →ₐ[𝕜] 𝕜, ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜),
    IsAlgebraicChart e ∧ p ∈ e.source

@[reducible]
noncomputable def HasAlgebraicCharts.chartedSpace (h : HasAlgebraicCharts 𝕜 A d) :
    ChartedSpace (Fin d → 𝕜) (A →ₐ[𝕜] 𝕜) where
  atlas := {e | IsAlgebraicChart e}
  chartAt p := (h p).choose
  mem_chart_source p := (h p).choose_spec.2
  chart_mem_atlas p := (h p).choose_spec.1

theorem IsAlgebraicChart.analyticOnNhd_trans
    {e e' : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜)} (he : IsAlgebraicChart e)
    (he' : IsAlgebraicChart e') : AnalyticOnNhd 𝕜 (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
  intro z hz
  obtain ⟨x', s', hx'⟩ := he'.exists_eq_div
  have hzt : z ∈ e.target := hz.1
  have hzs : e.symm z ∈ e'.source := hz.2
  have hev : ∀ᶠ w in 𝓝 z, e.symm w ∈ e'.source :=
    (e.continuousAt_symm hzt).preimage_mem_nhds (e'.open_source.mem_nhds hzs)
  have hq : AnalyticAt 𝕜 (fun w i => e.symm w (x' i) / e.symm w s') z := by
    rw [analyticAt_pi_iff]
    intro i
    exact (he.analyticOnNhd _ z hzt).div (he.analyticOnNhd _ z hzt) (hx' _ hzs).1
  refine hq.congr ?_
  filter_upwards [hev] with w hw
  funext i
  simp [(hx' _ hw).2 i]

variable [CompleteSpace 𝕜]

theorem HasAlgebraicCharts.isManifold (h : HasAlgebraicCharts 𝕜 A d) :
    letI := h.chartedSpace
    IsManifold 𝓘(𝕜, Fin d → 𝕜) ω (A →ₐ[𝕜] 𝕜) := by
  letI := h.chartedSpace
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.inter_univ]
  exact (IsAlgebraicChart.analyticOnNhd_trans he he').contDiffOn
    (e.symm ≫ₕ e').open_source.uniqueDiffOn

theorem HasAlgebraicCharts.contMDiff_eval (h : HasAlgebraicCharts 𝕜 A d) (a : A) :
    letI := h.chartedSpace
    ContMDiff 𝓘(𝕜, Fin d → 𝕜) 𝓘(𝕜) ω fun p : A →ₐ[𝕜] 𝕜 => p a := by
  letI := h.chartedSpace
  intro p
  have hc : IsAlgebraicChart (chartAt (Fin d → 𝕜) p) := chart_mem_atlas (Fin d → 𝕜) p
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps]
  rw [contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  exact (hc.analyticOnNhd a _ (mem_chart_target _ p)).contDiffAt

section Detect

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]

omit [CompleteSpace 𝕜] in
theorem mdifferentiableAt_pi_of_forall {ι : Type*} [Fintype ι] {f : M → ι → 𝕜} {x : M}
    (hf : ∀ i, MDifferentiableAt I 𝓘(𝕜) (fun m => f m i) x) :
    MDifferentiableAt I 𝓘(𝕜, ι → 𝕜) f x := by
  have h' := fun i => (mdifferentiableAt_iff _ _).1 (hf i)
  rw [mdifferentiableAt_iff]
  refine ⟨continuousAt_pi.2 fun i => (h' i).1, ?_⟩
  rw [differentiableWithinAt_pi]
  intro i
  exact (h' i).2

omit [CompleteSpace 𝕜] in
theorem HasAlgebraicCharts.exists_extChartAt_eventuallyEq (h : HasAlgebraicCharts 𝕜 A d)
    {φ : M → (A →ₐ[𝕜] 𝕜)} {m : M} (hφ : ContinuousAt φ m) :
    letI := h.chartedSpace
    ∃ (x : Fin d → A) (s : A), φ m s ≠ 0 ∧
      extChartAt 𝓘(𝕜, Fin d → 𝕜) (φ m) ∘ φ =ᶠ[𝓝 m] fun m' i => φ m' (x i) / φ m' s := by
  letI := h.chartedSpace
  have hc : IsAlgebraicChart (chartAt (Fin d → 𝕜) (φ m)) := chart_mem_atlas (Fin d → 𝕜) (φ m)
  obtain ⟨x, s, hxs⟩ := hc.exists_eq_div
  have hev : ∀ᶠ m' in 𝓝 m, φ m' ∈ (chartAt (Fin d → 𝕜) (φ m)).source :=
    hφ.preimage_mem_nhds ((chartAt (Fin d → 𝕜) (φ m)).open_source.mem_nhds (mem_chart_source _ _))
  refine ⟨x, s, (hxs _ (mem_chart_source _ _)).1, ?_⟩
  filter_upwards [hev] with m' hm'
  funext i
  simp [(hxs _ hm').2 i]

theorem HasAlgebraicCharts.mdifferentiable_iff (h : HasAlgebraicCharts 𝕜 A d)
    {φ : M → (A →ₐ[𝕜] 𝕜)} :
    letI := h.chartedSpace
    MDifferentiable I 𝓘(𝕜, Fin d → 𝕜) φ ↔ ∀ a, MDifferentiable I 𝓘(𝕜) fun m => φ m a := by
  letI := h.chartedSpace
  refine ⟨fun hφ a => ((h.contMDiff_eval a).mdifferentiable (by simp)).comp hφ, fun hφ m => ?_⟩
  have hcont : Continuous φ := GlobalTheory.AffinePoints.continuous_iff.2 fun a => (hφ a).continuous
  obtain ⟨x, s, hs, hev⟩ := h.exists_extChartAt_eventuallyEq (m := m) hcont.continuousAt
  rw [mdifferentiableAt_iff_target]
  refine ⟨hcont.continuousAt, ?_⟩
  have hq : MDifferentiableAt I 𝓘(𝕜, Fin d → 𝕜) (fun m' i => φ m' (x i) / φ m' s) m :=
    mdifferentiableAt_pi_of_forall fun i => ((hφ (x i)) m).div ((hφ s) m) hs
  exact hq.congr_of_eventuallyEq hev

end Detect

theorem exists_isAlgebraicChart_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), IsAlgebraicChart e ∧ p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g := by
  obtain ⟨e, hp, he, ha⟩ := exists_chart_of_etale g hg p
  refine ⟨e, ⟨⟨fun i => g (X i), 1, fun q _ => ⟨by simp, fun i => ?_⟩⟩, ha⟩, hp, he⟩
  rw [he]
  simp [coords]

theorem exists_isAlgebraicChart_of_away (s : A) (B : Type*) [CommRing B] [Algebra 𝕜 B]
    [Algebra A B] [IsScalarTower 𝕜 A B] [IsLocalization.Away s B]
    [Algebra.IsStandardSmoothOfRelativeDimension d 𝕜 B] (p : A →ₐ[𝕜] 𝕜) (hp : p s ≠ 0) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), IsAlgebraicChart e ∧ p ∈ e.source := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d 𝕜 B
  have hj : IsOpenEmbedding (comap (IsScalarTower.toAlgHom 𝕜 A B) : (B →ₐ[𝕜] 𝕜) → (A →ₐ[𝕜] 𝕜)) :=
    isOpenEmbedding_comap_away s
  obtain ⟨q, rfl⟩ : p ∈ range (comap (IsScalarTower.toAlgHom 𝕜 A B) : (B →ₐ[𝕜] 𝕜) → (A →ₐ[𝕜] 𝕜)) := by
    rw [range_comap_away s]
    exact hp
  have : Nonempty (B →ₐ[𝕜] 𝕜) := ⟨q⟩
  obtain ⟨F, hFs, hFt, hFc⟩ : ∃ F : OpenPartialHomeomorph (B →ₐ[𝕜] 𝕜) (A →ₐ[𝕜] 𝕜),
      F.source = univ ∧ F.target = range (comap (IsScalarTower.toAlgHom 𝕜 A B)) ∧
      ⇑F = comap (IsScalarTower.toAlgHom 𝕜 A B) :=
    ⟨IsOpenEmbedding.toOpenPartialHomeomorph _ hj, by simp, by simp, by simp⟩
  have hinv : ∀ q', F.symm (comap (IsScalarTower.toAlgHom 𝕜 A B) q') = q' := fun q' => by
    have := F.left_inv (x := q') (by rw [hFs]; trivial)
    rwa [hFc] at this
  obtain ⟨eB, heB, hqB, -⟩ := exists_isAlgebraicChart_of_etale g hg q
  obtain ⟨xB, sB, hB⟩ := heB.exists_eq_div
  obtain ⟨⟨b, hb⟩, hxb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers s) xB
  obtain ⟨⟨c, ⟨u, hu⟩⟩, hcu⟩ := IsLocalization.surj (Submonoid.powers s) sB
  have hxb' : ∀ i, ∃ a, algebraMap A B a = b • xB i := fun i => hxb i
  choose a ha using hxb'
  have hbu : IsUnit (algebraMap A B b) := IsLocalization.map_units B (⟨b, hb⟩ : Submonoid.powers s)
  have huu : IsUnit (algebraMap A B u) := IsLocalization.map_units B (⟨u, hu⟩ : Submonoid.powers s)
  refine ⟨F.symm.trans eB, ⟨⟨fun i => a i * u, c * b, ?_⟩, fun a' => ?_⟩, ?_⟩
  · rintro p' ⟨hp'1, hp'2⟩
    have hp'3 : p' ∈ F.target := hp'1
    rw [hFt] at hp'3
    obtain ⟨q', rfl⟩ := hp'3
    have hp'4 : F.symm (comap (IsScalarTower.toAlgHom 𝕜 A B) q') ∈ eB.source := hp'2
    rw [hinv] at hp'4
    have h1 : ∀ i, q' (xB i) = q' (algebraMap A B (a i)) / q' (algebraMap A B b) := fun i =>
      apply_eq_div_of_mul_eq q' hbu (by rw [ha i, Algebra.smul_def, mul_comm])
    have h2 : q' sB = q' (algebraMap A B c) / q' (algebraMap A B u) :=
      apply_eq_div_of_mul_eq q' huu hcu
    have hb0 : q' (algebraMap A B b) ≠ 0 := (hbu.map q').ne_zero
    have hu0 : q' (algebraMap A B u) ≠ 0 := (huu.map q').ne_zero
    have hs0 : q' sB ≠ 0 := (hB q' hp'4).1
    have hc0 : q' (algebraMap A B c) ≠ 0 := by
      intro h0
      rw [h2, h0, zero_div] at hs0
      exact hs0 rfl
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hinv, comap_apply,
      IsScalarTower.toAlgHom_apply, map_mul]
    refine ⟨mul_ne_zero hc0 hb0, fun i => ?_⟩
    rw [(hB q' hp'4).2 i, h1 i, h2]
    field_simp
  · have hfun : (fun z => (F.symm.trans eB).symm z a') = fun z => eB.symm z (algebraMap A B a') := by
      funext z
      simp [hFc, comap_apply]
    rw [hfun]
    exact (heB.analyticOnNhd _).mono fun z hz => hz.1
  · refine ⟨?_, ?_⟩
    · show _ ∈ F.target
      rw [hFt]
      exact mem_range_self q
    · show F.symm _ ∈ eB.source
      rw [hinv]
      exact hqB

theorem hasAlgebraicCharts_of_isStandardSmooth
    [Algebra.IsStandardSmoothOfRelativeDimension d 𝕜 A] : HasAlgebraicCharts 𝕜 A d := by
  intro p
  haveI : IsLocalization.Away (1 : A) A :=
    IsLocalization.away_of_isUnit_of_bijective A isUnit_one Function.bijective_id
  exact exists_isAlgebraicChart_of_away (1 : A) A p (by simp)

end GlobalTheory.AffinePoints
