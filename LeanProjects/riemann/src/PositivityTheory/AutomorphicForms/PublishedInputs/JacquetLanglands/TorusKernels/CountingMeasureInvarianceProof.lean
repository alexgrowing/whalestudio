import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.CountingMeasureInvariance

variable {G Ω X : Type} [Group G] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [Countable Ω]
  [MeasurableSpace X] [MulAction G Ω] [MulAction G X]

theorem meas_of_left {f : Ω × X → ℝ} (hf : ∀ ω, Measurable fun x => f (ω, x)) : Measurable f := by
  intro s hs
  have : f ⁻¹' s = ⋃ ω : Ω, ({ω} : Set Ω) ×ˢ ((fun x => f (ω, x)) ⁻¹' s) := by
    ext ⟨ω, x⟩; simp
  rw [this]
  exact MeasurableSet.iUnion fun ω => (MeasurableSet.of_discrete (s := {ω})).prod (hf ω hs)

omit [Countable Ω] in
theorem count_pres (g : G) :
    MeasurePreserving (fun ω : Ω => g • ω) Measure.count Measure.count := by
  have hm : ∀ h : G, Measurable (fun ω : Ω => h • ω) := fun h => Measurable.of_discrete
  refine ⟨hm g, le_antisymm ((MulAction.injective g).map_count_le (hm g)) ?_⟩
  calc (Measure.count : Measure Ω)
      = (Measure.count.map (fun ω : Ω => g⁻¹ • ω)).map (fun ω => g • ω) := by
        rw [Measure.map_map (hm g) (hm g⁻¹)]
        simp [Function.comp_def]
    _ ≤ Measure.count.map (fun ω : Ω => g • ω) :=
        Measure.map_mono ((MulAction.injective g⁻¹).map_count_le (hm _)) (hm g)

theorem pres_prod (μ : Measure X) [SigmaFinite μ] (hμ : Pres G μ) :
    Pres G ((Measure.count : Measure Ω).prod μ) := fun g =>
  (count_pres g).prod (hμ g)

open Classical in

def cut (R : Set Ω) (β : Ω → X → ℝ) (p : Ω × X) : ℝ := if p.1 ∈ R then β p.1 p.2 else 0

theorem cut_isCut (R : Set Ω) (hR : ∀ ω, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit G ω) (β : Ω → X → ℝ)
    (hβ : ∀ r ∈ R, IsCut (MulAction.stabilizer G r) (β r)) : IsCut G (cut R β) where
  meas := by
    refine meas_of_left fun ω => ?_
    by_cases h : ω ∈ R
    · simpa [cut, h] using (hβ ω h).meas
    · simp [cut, h]
  nonneg := by
    rintro ⟨ω, x⟩
    unfold cut
    split_ifs with h
    · exact (hβ _ h).nonneg x
    · exact le_rfl
  sum := by
    rintro ⟨ω, x⟩
    obtain ⟨r, ⟨hrR, g₀, hg₀'⟩, hu⟩ := hR ω
    have hg₀ : g₀ • ω = r := hg₀'
    have key : ∀ g : G, g • ω ∈ R → g • ω = r := fun g hg => hu _ ⟨hg, MulAction.mem_orbit ω g⟩
    let e : MulAction.stabilizer G r → G := fun s => (s : G) * g₀
    have he : Function.Injective e := fun s t h => Subtype.ext (mul_right_cancel h)
    rw [← he.hasSum_iff]
    · convert (hβ r hrR).sum (g₀ • x) using 1
      funext s
      have hs : (s : G) • r = r := s.2
      have h2 : ((s : G) * g₀) • ω = r := by rw [mul_smul, hg₀, hs]
      simp only [Function.comp_apply, e, cut, Prod.smul_mk, h2, mul_smul, Subgroup.smul_def]
      split_ifs with hc
      · rfl
      · exact absurd (h2.symm ▸ hrR) hc
    · intro g hg
      simp only [cut, Prod.smul_mk]
      rw [if_neg]
      intro hgR
      apply hg
      refine ⟨⟨g * g₀⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hg₀, inv_smul_smul, key g hgR, hg₀]
      · simp [e]

end UpperTheory.Esk.CountingMeasureInvariance

open UpperTheory.Esk.CountingMeasureInvariance in
theorem UpperTheory.Esk.counting_measure_invariance_proof : UpperTheory.Esk.C1 → UpperTheory.Esk.C4 := by
  intro hC1 G Ω X _ _ _ _ _ _ _ _ μ _ hμ b hb u hu hinv hint R hR β hβ
  have hP : Pres G ((Measure.count : Measure Ω).prod μ) := pres_prod μ hμ
  have hb' := cut_isCut R hR β hβ
  obtain ⟨hI', hE⟩ := (hC1 G (Ω × X) ((Measure.count : Measure Ω).prod μ) hP b (cut R β) hb hb').2
    u hu hinv hint
  have hsec : ∀ ω, Integrable (fun x => cut R β (ω, x) • u (ω, x)) μ := by
    have := hI'.prod_right_ae
    rwa [Measure.ae_count_iff] at this
  have hF : Integrable (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ) Measure.count :=
    hI'.integral_prod_left
  have hsum : HasSum (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ)
      (∫ y, b y • u y ∂((Measure.count : Measure Ω).prod μ)) := by
    rw [hE, integral_prod _ hI', integral_countable hF]
    simp only [count_real_singleton, one_smul]
    exact (integrable_count_iff.mp hF).of_norm.hasSum
  refine ⟨fun r hr => by simpa [cut, hr] using hsec r, ?_⟩
  have hsupp : Function.support (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ) ⊆ R := by
    intro ω hω
    by_contra h
    apply hω
    simp [cut, h]
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at hsum
  convert hsum using 1
  funext r
  simp [cut, r.2]
