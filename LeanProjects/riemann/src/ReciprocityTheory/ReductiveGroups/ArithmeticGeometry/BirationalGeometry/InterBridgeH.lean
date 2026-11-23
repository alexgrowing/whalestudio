import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) : Set (Fin e → ℂ) :=
  {u | u ∈ (A.chart j).target ∧ AnalyticAt ℂ (q ∘ (A.chart j).symm) u ∧
    LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0}

theorem isOpen_goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) :
    IsOpen (goodT A q j) := by
  rw [isOpen_iff_mem_nhds]
  rintro u ⟨hut, han, hdet⟩
  have h1 : ∀ᶠ v in 𝓝 u, v ∈ (A.chart j).target := (A.chart j).open_target.mem_nhds hut
  have h2 : ∀ᶠ v in 𝓝 u, AnalyticAt ℂ (q ∘ (A.chart j).symm) v := han.eventually_analyticAt
  have hc : ContinuousAt (fun v => ContinuousLinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) v)) u :=
    ContinuousLinearMap.continuous_det.continuousAt.comp han.fderiv.continuousAt
  have h3 : ∀ᶠ v in 𝓝 u, ContinuousLinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) v) ≠ 0 :=
    hc.eventually_ne hdet
  filter_upwards [h1, h2, h3] with v a b c
  exact ⟨a, b, c⟩

theorem target_diff_goodT_subset (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) :
    (A.chart j).target \ goodT A q j ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' S := by
  rintro u ⟨hut, hug⟩
  refine ⟨hut, ?_⟩
  by_contra hS
  apply hug
  have hx := (A.chart j).map_target hut
  have hr : (A.chart j) ((A.chart j).symm u) = u := (A.chart j).right_inv hut
  obtain ⟨h1, h2⟩ := hq _ hS j hx
  rw [hr] at h1 h2
  exact ⟨hut, h1, h2⟩

theorem integrableOn_chart [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Pt : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) *
      locDens A Φ j u) (A.chart j).target := by
  have hχc : ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
    have := ((Pt.smooth j) j).continuousOn
    simpa [Function.comp_def] using this
  have hKc : IsCompact ((A.chart j) '' tsupport (Pt.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (Pt.tsupport_subset j))
  have hKt : (A.chart j) '' tsupport (Pt.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (Pt.tsupport_subset j hx)
  have hI := hg j _ hKt hKc
  have hI2 : IntegrableOn (fun u => Pt.χ j ((A.chart j).symm u) *
      (g ((A.chart j).symm u) * locDens A Φ j u)) ((A.chart j) '' tsupport (Pt.χ j)) := by
    first
      | exact hI.continuousOn_mul (hχc.mono hKt) hKc
      | exact IntegrableOn.continuousOn_mul (hχc.mono hKt) hI hKc
  simp only [mul_assoc]
  refine hI2.of_forall_diff_eq_zero (A.chart j).open_target.measurableSet ?_
  rintro u ⟨hut, huK⟩
  have hn : (A.chart j).symm u ∉ tsupport (Pt.χ j) := fun h =>
    huK ⟨_, h, (A.chart j).right_inv hut⟩
  have h0 : Pt.χ j ((A.chart j).symm u) = 0 := by
    first
      | exact image_eq_zero_of_nmem_tsupport hn
      | exact image_eq_zero_of_notMem_tsupport hn
  rw [h0, zero_mul]

theorem goodT_fibre_eq (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) :
    goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y} =
      (A.chart j) '' ((A.chart j).source ∩ (q ⁻¹' {y} \ S)) := by
  ext u
  constructor
  · rintro ⟨hu, hy'⟩
    have hx := (A.chart j).map_target hu.1
    have hxS : (A.chart j).symm u ∉ S := fun hS => hy ⟨u, ⟨hu, hS⟩, hy'⟩
    exact ⟨(A.chart j).symm u, ⟨hx, hy', hxS⟩, (A.chart j).right_inv hu.1⟩
  · rintro ⟨x, ⟨hx, hqx, hxS⟩, rfl⟩
    have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
    obtain ⟨h1, h2⟩ := hq x hxS j hx
    refine ⟨⟨(A.chart j).map_source hx, h1, h2⟩, ?_⟩
    show q ((A.chart j).symm (A.chart j x)) ∈ ({y} : Set (Fin e → ℂ))
    rw [hl]
    exact hqx

theorem fib_term (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (Pt : ChartPartition A) (g : X → ℝ) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source)
    (hxS : x ∉ S) :
    Pt.χ j ((A.chart j).symm (A.chart j x)) * g ((A.chart j).symm (A.chart j x)) *
        locDens A Φ j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
      Pt.χ j x * (g x * pushDens A Φ q x) := by
  have hxc : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
  have hut : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart (chartIdx A x)).source :=
    ⟨hut, by
      show (A.chart j).symm (A.chart j x) ∈ (A.chart (chartIdx A x)).source
      rw [hl]
      exact hxc⟩
  have hD := locDensChart A Φ hΦ j (chartIdx A x) (A.chart j x) hut hmem.2
  rw [hl] at hD
  have hTan : AnalyticAt ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :=
    A.holo j (chartIdx A x) _ hmem
  have hTu : (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) = A.chart (chartIdx A x) x := by
    simp [hl]
  obtain ⟨hqc, -⟩ := hq x hxS (chartIdx A x) hxc
  obtain ⟨-, hdj⟩ := hq x hxS j hx
  have heq : (q ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j x)]
      (q ∘ (A.chart (chartIdx A x)).symm) ∘ (A.chart (chartIdx A x) ∘ (A.chart j).symm) := by
    have hopen : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart (chartIdx A x)).source ∈
        𝓝 (A.chart j x) :=
      ((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
        (A.chart (chartIdx A x)).open_source).mem_nhds hmem
    filter_upwards [hopen] with y hy
    simp only [Function.comp_apply]
    rw [(A.chart (chartIdx A x)).left_inv hy.2]
  have hfd : fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) =
      (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x)).comp
        (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x)) := by
    rw [heq.fderiv_eq, fderiv_comp _ (by rw [hTu]; exact hqc.differentiableAt)
      hTan.differentiableAt, hTu]
  have hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
    rw [hfd]
    exact LinearMap.det_comp _ _
  have hT0 : ‖LinearMap.det (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [hdet, h, mul_zero] at hdj
    exact hdj rfl
  have hQ0 : ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [hdet, h, zero_mul] at hdj
    exact hdj rfl
  rw [hl, jacN, pushDens, hD, hdet, norm_mul, mul_pow]
  field_simp

end ReciprocityTheory.ChartRestriction.G.Geo
