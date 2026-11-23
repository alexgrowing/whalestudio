import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyPartitionDensity
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixDens

theorem part_univ_ne_top {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {ρ : AlgChart p σ D → CxPts p σ → ℝ} (hp : IsProjOver p) (a : Nonempty (AnRead p σ D)) (h : IsDens ρ) :
    part ρ Set.univ ≠ ⊤ := by
  haveI := CxPts.compactSpace σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  obtain ⟨ν, w, hν, -, -, -, h1, h2⟩ := GlobalTheory.MixDens.exists_refMeasure k X p σ D a
  obtain ⟨g, hg, hgw⟩ := h1 ρ h
  rw [(h2 ρ g hg hgw).1, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable g ν := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  exact hi.lintegral_lt_top.ne

theorem part_compl_ptsIn {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X] {σ : k →+* ℂ} {D : ℕ}
    (hp : IsArithVar p D) (ρ : AlgChart p σ D → CxPts p σ → ℝ) (c : AlgChart p σ D) (hc : c.e.source.Nonempty) :
    part ρ (ptsIn p σ c.U)ᶜ = 0 := by
  have hmem : ∀ y : CxPts p σ, y ∈ ptsIn p σ c.U ↔ y.1 (IsLocalRing.closedPoint ℂ) ∈ c.U := by
    intro y
    constructor
    · intro hy
      exact hy (Set.mem_univ (IsLocalRing.closedPoint ℂ))
    · intro hy x _
      have : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact hy
  obtain ⟨y, hy⟩ := hc
  have hU : (c.U : Set X).Nonempty := ⟨_, (hmem y).1 (c.source_subset hy)⟩
  have hgen : genericPoint X ∉ (c.U : Set X)ᶜ := by
    intro h
    exact h (((genericPoint_spec X).mem_open_set_iff c.U.isOpen).2 (by simpa using hU))
  have := GlobalTheory.MixDensNull.part_over_closed k X p D hp (c.U : Set X)ᶜ c.U.isOpen.isClosed_compl hgen σ ρ
  refine measure_mono_null (fun x hx => ?_) this
  exact fun h => hx ((hmem x).2 h)

theorem measurePreserving_uncurry {ι : Type} [Fintype ι] {κ : ι → Type} [∀ a, Fintype (κ a)] :
    MeasurePreserving (MeasurableEquiv.piCurry fun a (_ : κ a) => ℂ).symm volume volume := by
  refine ⟨(MeasurableEquiv.piCurry _).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.piCurry _).symm.measurable (MeasurableSet.univ_pi hs)]
  have e : (MeasurableEquiv.piCurry fun a (_ : κ a) => ℂ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun a => Set.univ.pi fun j => s ⟨a, j⟩ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm]
    rfl
  rw [e, volume_pi_pi, Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun a _ => volume_pi_pi _

theorem measurePreserving_elim {τ : Type} [Fintype τ] :
    MeasurePreserving (fun (x : ℂ × (τ → ℂ)) (j : Option τ) => j.elim x.1 x.2) volume volume := by
  have hm : Measurable (fun (x : ℂ × (τ → ℂ)) (j : Option τ) => j.elim x.1 x.2) := by
    refine measurable_pi_lambda _ fun j => ?_
    cases j with
    | none => exact measurable_fst
    | some j => exact (measurable_pi_apply j).comp measurable_snd
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have e : (fun (x : ℂ × (τ → ℂ)) (j : Option τ) => j.elim x.1 x.2) ⁻¹' Set.univ.pi s =
      s none ×ˢ Set.univ.pi fun j => s (some j) := by
    ext x
    simp [Option.forall]
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, Fintype.prod_option]

theorem measurePreserving_pt {ι : Type} [Fintype ι] {r : ι → ℕ} {d : ℕ}
    (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) :
    MeasurePreserving (fun x : V 1 × (∀ a, Low (r a) → ℂ) => pt e x.1 x.2) volume volume := by
  have h1 : MeasurePreserving (fun z : V 1 => z 0) volume volume :=
    (volume_preserving_funUnique (Fin 1) ℂ).comp (volume_preserving_ofLp_complex (Fin 1))
  have h2 := h1.prod (measurePreserving_uncurry (κ := fun a => Low (r a)))
  have h3 := (measurePreserving_elim (τ := Σ a, Low (r a))).comp h2
  have h4 := (volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin (d + 1)))
  have h6 := h5.comp h4
  exact h6

theorem continuous_base {ι : Type} {r : ι → ℕ} {d : ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) :
    Continuous (base e) := by
  unfold base
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact (continuous_single (A := fun _ : Fin 1 => ℂ) 0).comp (by fun_prop)

theorem setIntegral_base {ι : Type} [Fintype ι] {r : ι → ℕ} {d : ℕ}
    (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) {F : V (d + 1) → ℝ} {G : V 1 → ℝ} {K : Set (V 1)}
    (hK : MeasurableSet K) (hF : IntegrableOn F (base e ⁻¹' K))
    (hG : ∀ z ∈ K, ∫ n : ∀ a, Low (r a) → ℂ, F (pt e z n) = G z) :
    ∫ v in base e ⁻¹' K, F v = ∫ z in K, G z := by
  have hm := (measurePreserving_pt e).restrict_preimage ((continuous_base e).measurable hK)
  have hs : (fun x : V 1 × (∀ a, Low (r a) → ℂ) => pt e x.1 x.2) ⁻¹' (base e ⁻¹' K) = K ×ˢ Set.univ := by
    ext x
    simp [base_pt]
  rw [hs] at hm
  have hi := hm.integrable_comp_of_integrable hF
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable (by rw [hm.map_eq]; exact hF.aestronglyMeasurable)]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod (fun x : V 1 × (∀ a, Low (r a) → ℂ) => F (pt e x.1 x.2)) hi]
  refine setIntegral_congr_fun hK fun z hz => ?_
  simp only [Measure.restrict_univ]
  exact hG z hz

theorem integrable_of_parts {α : Type} [MeasurableSpace α] {μ : Measure α} {F : α → ℝ}
    (hF : AEStronglyMeasurable F μ) (h₁ : ∫⁻ v, ENNReal.ofReal (F v) ∂μ ≠ ⊤)
    (h₂ : ∫⁻ v, ENNReal.ofReal (-F v) ∂μ ≠ ⊤) : Integrable F μ := by
  refine ⟨hF, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ v, ENNReal.ofReal ‖F v‖ ∂μ ≤ ∫⁻ v, (ENNReal.ofReal (F v) + ENNReal.ofReal (-F v)) ∂μ := by
        refine lintegral_mono fun v => ?_
        rcases abs_choice (F v) with h | h <;> rw [Real.norm_eq_abs, h]
        · exact le_self_add
        · exact le_add_self
    _ = ∫⁻ v, ENNReal.ofReal (F v) ∂μ + ∫⁻ v, ENNReal.ofReal (-F v) ∂μ :=
        lintegral_add_left' hF.aemeasurable.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩

section Cell

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {π : Y ⟶ B} {w : π ≫ q = p}
  {ι : Type} [Fintype ι] {r : ι → ℕ} {d : ℕ} {e : Fin (d + 1) ≃ Option (Σ a, Low (r a))} {σ : k →+* ℂ}
  {c : AlgChart q σ 1} {c' : AlgChart p σ (d + 1)}

omit [Fintype ι] in

theorem IsCell.image_eq (h : IsCell e π w c c') {A : Set (CxPts q σ)} (hA : A ⊆ c.e.source) :
    c'.e '' (PtsOver.map π w (spMap σ) ⁻¹' A ∩ c'.e.source) = base e ⁻¹' (c.e '' A) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  ext v
  constructor
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    exact ⟨_, hy, (h₃ y hy').symm⟩
  · rintro ⟨a, ha, hv⟩
    have hvt : v ∈ c'.e.target := by
      rw [h₂]
      change base e v ∈ c.e.target
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

theorem IsCell.part_preimage [IsIntegral Y] [SecondCountableTopology (CxPts p σ)] (h : IsCell e π w c c')
    (hp : IsArithVar p (d + 1)) {ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ} (hρ : IsDens ρ)
    {A : Set (CxPts q σ)} (hAm : MeasurableSet A) (hA : A ⊆ c.e.source) :
    part ρ (PtsOver.map π w (spMap σ) ⁻¹' A) =
      ∫⁻ v in base e ⁻¹' (c.e '' A), ENNReal.ofReal (ρ c' (c'.e.symm v)) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have hne : c'.e.source.Nonempty := by
    refine ⟨c'.e.symm (pt e (c.e a) 0), c'.e.map_target ?_⟩
    rw [h.2.1]
    change base e _ ∈ c.e.target
    rw [base_pt]
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
    (h : IsCell e π w c c') (hp : IsArithVar p (d + 1)) {ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ}
    {g : AlgChart q σ 1 → CxPts q σ → ℝ} (hρ : IsDens ρ) (hg : IsDens g) (f₁ : part ρ Set.univ ≠ ⊤)
    (f₂ : part (fun c y => -ρ c y) Set.univ ≠ ⊤) (f₃ : part g Set.univ ≠ ⊤)
    (f₄ : part (fun c y => -g c y) Set.univ ≠ ⊤)
    (hfib : ∀ z ∈ c.e.target, ∫ n : ∀ a, Low (r a) → ℂ, ρ c' (c'.e.symm (pt e z n)) = g c (c.e.symm z))
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
  have hT : base e ⁻¹' (c.e '' A) ⊆ c'.e.target := by
    rw [h.2.1]
    exact fun v hv => hKt hv
  have i₁ := integrable_of_parts
    (((hρ.2 c').mono hT).aestronglyMeasurable ((continuous_base e).measurable hK)) g₁ g₂
  have i₂ := integrable_of_parts (((hg.2 c).mono hKt).aestronglyMeasurable hK) g₃ g₄
  have key := setIntegral_base e hK i₁ fun z hz => hfib z (hKt hz)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part i₁,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part i₂] at key
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.2 ⟨g₁, g₄⟩) (ENNReal.add_ne_top.2 ⟨g₂, g₃⟩),
    ENNReal.toReal_add g₁ g₄, ENNReal.toReal_add g₂ g₃]
  linarith

end Cell

theorem total_eq_of_cells : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) [IsIntegral Y], IsArithVar q 1 → IsArithVar p (d + 1) → Nonempty (AnRead q σ 1) → Nonempty (AnRead p σ (d + 1)) → ∀ (ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ) (g : AlgChart q σ 1 → CxPts q σ → ℝ), IsDens ρ → IsDens g → (∀ y : CxPts q σ, ∃ (c : AlgChart q σ 1) (c' : AlgChart p σ (d + 1)), y ∈ c.e.source ∧ IsCell e π w c c' ∧ ∀ z ∈ c.e.target, ∫ n : ∀ a, Low (r a) → ℂ, ρ c' (c'.e.symm (pt e z n)) = g c (c.e.symm z)) → total ρ = total g := by
  intro k _ B Y q p π w ι _ r d e σ _ hq hp aq ap ρ g hρ hg hcov
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

end GlobalTheory.MixDens
