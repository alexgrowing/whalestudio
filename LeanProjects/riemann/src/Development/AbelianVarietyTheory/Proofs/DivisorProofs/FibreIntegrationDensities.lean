import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.BigCell

theorem measurePreserving_pt {ι : Type} [Fintype ι] {r : ι → ℕ} {n D : ℕ}
    (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) :
    MeasurePreserving (fun x : V n × (∀ a, Low (r a) → ℂ) => BigCell.pt ε x.1 x.2) volume volume := by
  have h1 : MeasurePreserving (fun z : V n => (WithLp.ofLp z : Fin n → ℂ)) volume volume :=
    volume_preserving_ofLp_complex (Fin n)
  have h2 := h1.prod (measurePreserving_uncurry (κ := fun a => Low (r a)))
  have h3 := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ (Σ a, Low (r a)) => ℂ)).comp h2
  have h4 := (volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin D))
  have h6 := h5.comp h4
  exact h6

theorem continuous_base {ι : Type} {r : ι → ℕ} {n D : ℕ} (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) :
    Continuous (BigCell.base ε) :=
  (BigCell.baseL ε).continuous

theorem setIntegral_base {ι : Type} [Fintype ι] {r : ι → ℕ} {n D : ℕ}
    (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) {F : V D → ℝ} {G : V n → ℝ} {K : Set (V n)}
    (hK : MeasurableSet K) (hF : IntegrableOn F (BigCell.base ε ⁻¹' K))
    (hG : ∀ z ∈ K, ∫ u : ∀ a, Low (r a) → ℂ, F (BigCell.pt ε z u) = G z) :
    ∫ v in BigCell.base ε ⁻¹' K, F v = ∫ z in K, G z := by
  have hm := (measurePreserving_pt ε).restrict_preimage ((continuous_base ε).measurable hK)
  have hs : (fun x : V n × (∀ a, Low (r a) → ℂ) => BigCell.pt ε x.1 x.2) ⁻¹' (BigCell.base ε ⁻¹' K) =
      K ×ˢ Set.univ := by
    ext x
    simp [BigCell.base_pt]
  rw [hs] at hm
  have hi := hm.integrable_comp_of_integrable hF
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable (by rw [hm.map_eq]; exact hF.aestronglyMeasurable)]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod (fun x : V n × (∀ a, Low (r a) → ℂ) => F (BigCell.pt ε x.1 x.2)) hi]
  refine setIntegral_congr_fun hK fun z hz => ?_
  simp only [Measure.restrict_univ]
  exact hG z hz

section Cell

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {π : Y ⟶ B} {w : π ≫ q = p}
  {ι : Type} [Fintype ι] {r : ι → ℕ} {n D : ℕ} {ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))} {σ : k →+* ℂ}
  {c : AlgChart q σ n} {c' : AlgChart p σ D}

omit [Fintype ι] in

theorem IsCell.image_eq (h : BigCell.IsCell ε π w c c') {A : Set (CxPts q σ)} (hA : A ⊆ c.e.source) :
    c'.e '' (PtsOver.map π w (spMap σ) ⁻¹' A ∩ c'.e.source) = BigCell.base ε ⁻¹' (c.e '' A) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  ext v
  constructor
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    exact ⟨_, hy, (h₃ y hy').symm⟩
  · rintro ⟨a, ha, hv⟩
    have hvt : v ∈ c'.e.target := by
      rw [h₂]
      change BigCell.base ε v ∈ c.e.target
      rw [← hv]
      exact c.e.map_source (hA ha)
    have hy := c'.e.map_target hvt
    refine ⟨c'.e.symm v, ⟨?_, hy⟩, c'.e.right_inv hvt⟩
    have h₄ := h₃ _ hy
    rw [c'.e.right_inv hvt, ← hv] at h₄
    have h₅ : PtsOver.map π w (spMap σ) (c'.e.symm v) ∈ c.e.source := (h₁ ▸ hy).1
    have := c.e.injOn (hA ha) h₅ h₄
    change PtsOver.map π w (spMap σ) (c'.e.symm v) ∈ A
    rw [← this]
    exact ha

omit [Fintype ι] in

theorem IsCell.part_preimage [IsIntegral Y] [SecondCountableTopology (CxPts p σ)] (h : BigCell.IsCell ε π w c c')
    (hp : IsArithVar p D) {ρ : AlgChart p σ D → CxPts p σ → ℝ} (hρ : IsDens ρ)
    {A : Set (CxPts q σ)} (hAm : MeasurableSet A) (hA : A ⊆ c.e.source) :
    part ρ (PtsOver.map π w (spMap σ) ⁻¹' A) =
      ∫⁻ v in BigCell.base ε ⁻¹' (c.e '' A), ENNReal.ofReal (ρ c' (c'.e.symm v)) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have hne : c'.e.source.Nonempty := by
    refine ⟨c'.e.symm (BigCell.pt ε (c.e a) 0), c'.e.map_target ?_⟩
    rw [h.2.1]
    change BigCell.base ε _ ∈ c.e.target
    rw [BigCell.base_pt]
    exact c.e.map_source (hA ha)
  have hm : MeasurableSet (PtsOver.map π w (spMap σ) ⁻¹' A) :=
    (PtsOver.continuous_map π w (spMap σ)).measurable hAm
  rw [← h.image_eq hA, ← hρ.part_apply c' (hm.inter c'.e.open_source.measurableSet) Set.inter_subset_right,
    ← measure_inter_add_sdiff _ c'.e.open_source.measurableSet]
  have h0 : part ρ (PtsOver.map π w (spMap σ) ⁻¹' A \ c'.e.source) = 0 := by
    refine measure_mono_null (fun y hy => ?_) (part_compl_ptsIn hp ρ c' hne)
    intro hU
    refine hy.2 ?_
    rw [h.1]
    exact ⟨hA hy.1, hU⟩
  rw [h0, add_zero]

theorem IsCell.part_add_part [IsIntegral Y] [SecondCountableTopology (CxPts q σ)] [SecondCountableTopology (CxPts p σ)]
    (h : BigCell.IsCell ε π w c c') (hp : IsArithVar p D) {ρ : AlgChart p σ D → CxPts p σ → ℝ}
    {g : AlgChart q σ n → CxPts q σ → ℝ} (hρ : IsDens ρ) (hg : IsDens g) (f₁ : part ρ Set.univ ≠ ⊤)
    (f₂ : part (fun c y => -ρ c y) Set.univ ≠ ⊤) (f₃ : part g Set.univ ≠ ⊤)
    (f₄ : part (fun c y => -g c y) Set.univ ≠ ⊤)
    (hfib : ∀ z ∈ c.e.target, ∫ u : ∀ a, Low (r a) → ℂ, ρ c' (c'.e.symm (BigCell.pt ε z u)) = g c (c.e.symm z))
    {A : Set (CxPts q σ)} (hAm : MeasurableSet A) (hA : A ⊆ c.e.source) :
    part ρ (PtsOver.map π w (spMap σ) ⁻¹' A) + part (fun c y => -g c y) A =
      part (fun c y => -ρ c y) (PtsOver.map π w (spMap σ) ⁻¹' A) + part g A := by
  have hρ' : IsDens fun c y => -ρ c y := (isDens_zero.sub hρ).congr fun c y _ => by simp
  have hg' : IsDens fun c y => -g c y := (isDens_zero.sub hg).congr fun c y _ => by simp
  have g₁ := ne_top_of_le_ne_top f₁ (measure_mono (Set.subset_univ (PtsOver.map π w (spMap σ) ⁻¹' A)))
  have g₂ := ne_top_of_le_ne_top f₂ (measure_mono (Set.subset_univ (PtsOver.map π w (spMap σ) ⁻¹' A)))
  have g₃ := ne_top_of_le_ne_top f₃ (measure_mono (Set.subset_univ A))
  have g₄ := ne_top_of_le_ne_top f₄ (measure_mono (Set.subset_univ A))
  rw [h.part_preimage hp hρ hAm hA] at g₁ ⊢
  rw [h.part_preimage hp hρ' hAm hA] at g₂ ⊢
  rw [hg.part_apply c hAm hA] at g₃ ⊢
  rw [hg'.part_apply c hAm hA] at g₄ ⊢
  have hK : MeasurableSet (c.e '' A) := ChartGlue.measurableSet_image c.e hAm hA
  have hKt : c.e '' A ⊆ c.e.target := by
    rintro _ ⟨a, ha, rfl⟩
    exact c.e.map_source (hA ha)
  have hT : BigCell.base ε ⁻¹' (c.e '' A) ⊆ c'.e.target := by
    rw [h.2.1]
    exact fun v hv => hKt hv
  have i₁ := integrable_of_parts
    (((hρ.2 c').mono hT).aestronglyMeasurable ((continuous_base ε).measurable hK)) g₁ g₂
  have i₂ := integrable_of_parts (((hg.2 c).mono hKt).aestronglyMeasurable hK) g₃ g₄
  have key := setIntegral_base ε hK i₁ fun z hz => hfib z (hKt hz)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part i₁,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part i₂] at key
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.2 ⟨g₁, g₄⟩) (ENNReal.add_ne_top.2 ⟨g₂, g₃⟩),
    ENNReal.toReal_add g₁ g₄, ENNReal.toReal_add g₂ g₃]
  linarith

end Cell

theorem total_eq_of_cells : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (σ : k →+* ℂ) [IsIntegral Y], IsArithVar q n → IsArithVar p D → Nonempty (AnRead q σ n) → Nonempty (AnRead p σ D) → ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : AlgChart q σ n → CxPts q σ → ℝ), IsDens ρ → IsDens g → (∀ y : CxPts q σ, ∃ (c : AlgChart q σ n) (c' : AlgChart p σ D), y ∈ c.e.source ∧ BigCell.IsCell ε π w c c' ∧ ∀ z ∈ c.e.target, ∫ u : ∀ a, Low (r a) → ℂ, ρ c' (c'.e.symm (BigCell.pt ε z u)) = g c (c.e.symm z)) → total ρ = total g := by
  intro k _ B Y q p π w ι _ r n D ε σ _ hq hp aq ap ρ g hρ hg hcov
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hq.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp.isProjOver
  have hρ' : IsDens fun c y => -ρ c y := (isDens_zero.sub hρ).congr fun c y _ => by simp
  have hg' : IsDens fun c y => -g c y := (isDens_zero.sub hg).congr fun c y _ => by simp
  have f1 := part_univ_ne_top hp.isProjOver ap hρ
  have f2 := part_univ_ne_top hp.isProjOver ap hρ'
  have f3 := part_univ_ne_top hq.isProjOver aq hg
  have f4 := part_univ_ne_top hq.isProjOver aq hg'
  set Φ := PtsOver.map π w (spMap σ) with hΦ
  have hΦm : Measurable Φ := (PtsOver.continuous_map π w (spMap σ)).measurable
  have key : (part ρ).map Φ + part (fun c y => -g c y) = (part (fun c y => -ρ c y)).map Φ + part g := by
    refine ChartGlue.ext_of_cover (fun y => (hcov y).choose.e.source) (fun y => (hcov y).choose.e.open_source)
      (fun y => ⟨y, (hcov y).choose_spec.choose_spec.1⟩) fun y A hA hAy => ?_
    obtain ⟨c', -, hcell, hfib⟩ := (hcov y).choose_spec
    rw [Measure.add_apply, Measure.add_apply, Measure.map_apply hΦm hA, Measure.map_apply hΦm hA]
    exact hcell.part_add_part hp hρ hg f1 f2 f3 f4 hfib hA hAy
  have hu := congrArg (fun μ => μ Set.univ) key
  simp only [Measure.add_apply, Measure.map_apply hΦm MeasurableSet.univ, Set.preimage_univ] at hu
  have := congrArg ENNReal.toReal hu
  rw [ENNReal.toReal_add f1 f4, ENNReal.toReal_add f2 f3] at this
  simp only [total]
  linarith

end GlobalTheory.BigCell
