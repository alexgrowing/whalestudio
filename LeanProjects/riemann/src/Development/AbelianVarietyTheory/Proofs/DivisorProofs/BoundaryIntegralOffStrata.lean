import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetInterPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionChartInjectiveDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UpMeas

section Analytic

open Set Filter Topology MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.TruncCoord GlobalTheory.RegToResolution
open scoped ENNReal

theorem exists_local_biholo {d : ℕ} {θ : (Fin d → ℂ) → Fin d → ℂ} {a : Fin d → ℂ} (hθ : AnalyticAt ℂ θ a)
    (J : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) (hJ : fderiv ℂ θ a = J) :
    ∃ Θ : OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ), ⇑Θ = θ ∧ a ∈ Θ.source ∧ AnalyticOnNhd ℂ Θ Θ.source ∧
      AnalyticOnNhd ℂ Θ.symm Θ.target := by
  have hs : HasStrictFDerivAt θ (J : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) a := hJ ▸ hθ.hasStrictFDerivAt
  let Θ₀ := hs.toOpenPartialHomeomorph θ
  have ha : a ∈ Θ₀.source := hs.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt ℂ Θ₀.symm (Θ₀ a) := Θ₀.analyticAt_symm' ha hθ hJ
  have hO : IsOpen ({x | AnalyticAt ℂ θ x} ∩ (Θ₀.source ∩ Θ₀ ⁻¹' {w | AnalyticAt ℂ Θ₀.symm w})) :=
    (isOpen_analyticAt ℂ θ).inter (Θ₀.isOpen_inter_preimage (isOpen_analyticAt ℂ _))
  refine ⟨Θ₀.restrOpen _ hO, rfl, ⟨ha, hθ, ha, hsymm⟩, fun x hx => hx.2.1, fun w hw => ?_⟩
  have h := hw.2.2.2
  rw [mem_preimage, mem_setOf_eq] at h
  change AnalyticAt ℂ Θ₀.symm (Θ₀ (Θ₀.symm w)) at h
  rwa [Θ₀.right_inv hw.1] at h

theorem exists_equiv_pad {n d : ℕ} (L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (hL : Function.Injective L) :
    n ≤ d ∧ ∃ J : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ), ∀ z, J (padZero n d z) = L z := by
  have hnd : n ≤ d := by simpa using LinearMap.finrank_le_finrank_of_injective (f := L.toLinearMap) hL
  refine ⟨hnd, ?_⟩
  obtain ⟨p, hp⟩ : ∃ p : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ), padZero n d = p := ⟨_, padZero_eq_clm n d⟩
  have hpi : Function.Injective p.toLinearMap := fun z w h => by
    have := congrArg (truncCoord n d) (show p z = p w from h)
    rwa [← hp, truncCoord_padZero hnd, truncCoord_padZero hnd] at this
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.ofInjective p.toLinearMap hpi).symm.trans (LinearEquiv.ofInjective L.toLinearMap hL))
  refine ⟨g.toContinuousLinearEquiv, fun z => ?_⟩
  have := hg (LinearEquiv.ofInjective p.toLinearMap hpi z)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.ofInjective_apply] at this
  rw [hp]
  exact this.symm

variable {d n : ℕ} {X M : Type} [TopologicalSpace X] [TopologicalSpace M]

theorem exists_straightening (A : FinHolAtlas d X) {u : M → X} (hu : IsInducing u)
    (e : OpenPartialHomeomorph M (Fin n → ℂ)) {y : M} (hy : y ∈ e.source)
    (χ : OpenPartialHomeomorph X (Fin d → ℂ)) (hχ : IsCompatChart A χ) (hχy : u y ∈ χ.source)
    (hF : AnalyticAt ℂ (χ ∘ u ∘ e.symm) (e y)) (hinj : Function.Injective (fderiv ℂ (χ ∘ u ∘ e.symm) (e y)))
    {Z W : Set X} (hW : IsOpen W) (hyW : u y ∈ W) (hZ : W ∩ range u = W ∩ Z) :
    ∃ ψ, IsStraightening A Z n ψ ∧ u y ∈ ψ.source ∧
      ∀ m, u m ∈ ψ.source → m ∈ e.source ∧ u m ∈ Z ∧ ψ (u m) = padZero n d (e m) := by
  set F := χ ∘ u ∘ e.symm with hFd
  obtain ⟨hnd, J, hJ⟩ := exists_equiv_pad _ hinj
  obtain ⟨p, hp⟩ : ∃ p : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ), padZero n d = p := ⟨_, padZero_eq_clm n d⟩
  have htp : ∀ z, truncCoord n d (p z) = z := fun z => hp ▸ truncCoord_padZero hnd z
  let K : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (J : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)).comp (ContinuousLinearMap.id ℂ _ - p.comp (truncCoord n d))
  let θ : (Fin d → ℂ) → Fin d → ℂ := fun v => F (truncCoord n d v) + K v
  have hθp : ∀ z, θ (p z) = F z := fun z => by simp [θ, K, htp]
  have hF' : AnalyticAt ℂ F (truncCoord n d (p (e y))) := by rwa [htp]
  have hθ : AnalyticAt ℂ θ (p (e y)) := (hF'.comp ((truncCoord n d).analyticAt _)).add (K.analyticAt _)
  have hθJ : fderiv ℂ θ (p (e y)) = J := by
    have := (hF'.differentiableAt.hasFDerivAt.comp _ (truncCoord n d).hasFDerivAt).add K.hasFDerivAt
    refine this.fderiv.trans ?_
    ext1 v
    simp [K, htp, ← hJ, hp]
  obtain ⟨Θ, hΘ, ha, hΘ₁, hΘ₂⟩ := exists_local_biholo hθ J hθJ
  obtain ⟨O₁, hO₁, hO₁e⟩ := hu.isOpen_iff.1 (e.isOpen_inter_preimage (Θ.open_source.preimage p.continuous))
  let ψ₀ := χ.trans Θ.symm
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' (u ⁻¹' (χ.source ∩ W))) :=
    e.isOpen_inter_preimage_symm ((χ.open_source.inter hW).preimage hu.continuous)
  have hO := (hW.inter hO₁).inter (ψ₀.isOpen_inter_preimage (hT.preimage (truncCoord n d).continuous))
  have key : ∀ m, u m ∈ O₁ → m ∈ e.source ∧ χ (u m) ∈ Θ.target ∧ ψ₀ (u m) = p (e m) := fun m hm => by
    have hm' : m ∈ e.source ∩ e ⁻¹' (p ⁻¹' Θ.source) := hO₁e ▸ hm
    have h₁ : χ (u m) = Θ (p (e m)) := by rw [hΘ, hθp, hFd]; simp [e.left_inv hm'.1]
    refine ⟨hm'.1, h₁ ▸ Θ.map_source hm'.2, ?_⟩
    change Θ.symm (χ (u m)) = _
    rw [h₁, Θ.left_inv hm'.2]
  have hy₁ : u y ∈ O₁ := show y ∈ u ⁻¹' O₁ from hO₁e ▸ ⟨hy, ha⟩
  have hy₀ : u y ∈ ψ₀.source := ⟨hχy, (key y hy₁).2.1⟩
  refine ⟨ψ₀.restrOpen _ hO, ⟨hnd, fun k => ⟨fun v hv => ?_, fun v hv => ?_⟩, ?_⟩, ⟨hy₀, ⟨hyW, hy₁⟩, hy₀, ?_⟩,
    fun m hm => ⟨(key m hm.2.1.2).1, (hZ.le ⟨hm.2.1.1, m, rfl⟩).2, hp ▸ (key m hm.2.1.2).2.2⟩⟩
  · exact AnalyticAt.comp (g := Θ.symm) (f := χ ∘ (A.chart k).symm) (hΘ₂ _ hv.2.1.2) ((hχ k).1 v ⟨hv.1, hv.2.1.1⟩)
  · exact AnalyticAt.comp (g := A.chart k ∘ χ.symm) (f := Θ) ((hχ k).2 (Θ v) ⟨hv.1.1.2, hv.2⟩) (hΘ₁ v hv.1.1.1)
  · ext x
    refine ⟨fun hx => ⟨hx.2, fun k hk => ?_⟩, fun hx => ⟨?_, hx.1⟩⟩
    · obtain ⟨m, rfl⟩ := (hZ.ge ⟨hx.2.2.1.1, hx.1⟩).2
      change ψ₀ (u m) k = 0
      rw [(key m hx.2.2.1.2).2.2, ← hp]
      simp [padZero, not_lt.2 hk]
    · have h₁ : p (truncCoord n d (ψ₀ x)) = ψ₀ x := hp ▸ padZero_truncCoord _ hx.2
      have h₂ : truncCoord n d (ψ₀ x) ∈ e.target ∩ e.symm ⁻¹' (u ⁻¹' (χ.source ∩ W)) := hx.1.2.2.2
      have h₃ : χ x = χ (u (e.symm (truncCoord n d (ψ₀ x)))) := by
        change _ = F _
        rw [← hθp, h₁, ← hΘ]
        exact (Θ.right_inv hx.1.1.2).symm
      have h₄ := χ.injOn hx.1.1.1 h₂.2.1 h₃
      exact (hZ.le ⟨hx.1.2.1.1, _, h₄.symm⟩).2
  · rw [mem_preimage, mem_preimage, (key y hy₁).2.2, htp]
    exact ⟨e.map_source hy, by simpa [e.left_inv hy] using ⟨hχy, hyW⟩⟩

theorem lintegral_le_sum [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (A : FinHolAtlas d X) {m : ℕ}
    (Zs S : Fin m → Set X) (P : LocPot X) (f : X → ℝ≥0∞) (μ : Measure M) {u : M → X} (hu : Function.Injective u)
    {G : Set M} (hG : μ Gᶜ = 0)
    (h : ∀ y ∈ G, ∃ N : Set M, IsOpen N ∧ y ∈ N ∧ ∃ (a : Fin m) (ψ : OpenPartialHomeomorph X (Fin d → ℂ))
      (e : M → Fin n → ℂ), IsStraightening A (Zs a) n ψ ∧
      (∀ x ∈ N, padZero n d (e x) ∈ ψ.target ∧ param n ψ (e x) = u x ∧ u x ∈ S a) ∧
      ∀ B, MeasurableSet B → B ⊆ N → MeasurableSet (e '' B) ∧
        ∫⁻ x in B, f (u x) ∂μ ≤ ∫⁻ z in e '' B, f (param n ψ z) * ‖paramDens n P ψ z‖ₑ) :
    ∫⁻ x, f (u x) ∂μ ≤ ∑ a, regIntegral A (Zs a) n P (S a) f := by
  classical
  rcases G.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · rw [compl_empty, Measure.measure_univ_eq_zero] at hG
    simp [hG]
  choose N hN hyN a ψ e hψ hx hB using fun y : G => h y y.2
  obtain ⟨T, hT, hTS⟩ := TopologicalSpace.isOpen_iUnion_countable N hN
  obtain ⟨g, hg⟩ := (hT.insert ⟨y₀, hy₀⟩).exists_eq_range (insert_nonempty _ _)
  set D := disjointed (N ∘ g) with hD
  have hDm : ∀ k, MeasurableSet (D k) := MeasurableSet.disjointed fun k => (hN _).measurableSet
  have hDN : ∀ k, D k ⊆ N (g k) := disjointed_subset (N ∘ g)
  have hcov : G ⊆ ⋃ k, D k := by
    rw [hD, iUnion_disjointed]
    intro y hy
    obtain ⟨l, hl, hy⟩ := mem_iUnion₂.1 (hTS.ge (mem_iUnion.2 ⟨⟨y, hy⟩, hyN _⟩))
    obtain ⟨k, rfl⟩ := hg.le (mem_insert_of_mem _ hl)
    exact mem_iUnion.2 ⟨k, hy⟩
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ k, D k := measure_mono_null (compl_subset_compl.2 hcov) hG
  rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_iUnion hDm (disjoint_disjointed _)]
  refine ENNReal.tsum_le_of_sum_range_le fun r => ?_
  rw [← Finset.sum_fiberwise (s := Finset.range r) (g := fun k => a (g k))]
  refine Finset.sum_le_sum fun b _ => ?_
  set s := (Finset.range r).filter fun k => a (g k) = b with hs
  let ι : Fin s.card → ℕ := fun j => s.equivFin.symm j
  have hι : ∀ j, a (g (ι j)) = b := fun j => (Finset.mem_filter.1 (s.equivFin.symm j).2).2
  have him : ∀ k, param n (ψ (g k)) '' (e (g k) '' D k) = u '' D k := fun k => by
    rw [image_image]
    exact image_congr fun x hx' => (hx _ x (hDN k hx')).2.1
  have hfam : IsPieceFamily A (Zs b) n (S b) (fun j => ψ (g (ι j))) fun j => e (g (ι j)) '' D (ι j) := by
    refine ⟨fun j => hι j ▸ hψ _, fun j => (hB _ _ (hDm _) (hDN _)).1, ?_, fun i j hij => ?_⟩
    · rintro j _ ⟨x, hx', rfl⟩
      obtain ⟨h₁, h₂, h₃⟩ := hx _ x (hDN _ hx')
      exact ⟨h₁, by rw [h₂, ← hι j]; exact h₃⟩
    · show Disjoint (param n (ψ (g (ι i))) '' (e (g (ι i)) '' D (ι i)))
        (param n (ψ (g (ι j))) '' (e (g (ι j)) '' D (ι j)))
      rw [him, him]
      exact (disjoint_image_iff hu).2 (disjoint_disjointed _ fun h => hij
        (s.equivFin.symm.injective (Subtype.ext h)))
  refine le_iSup_of_le s.card (le_iSup_of_le _ (le_iSup_of_le _ (le_iSup_of_le hfam ?_)))
  rw [← Finset.sum_coe_sort s, ← s.equivFin.symm.sum_comp]
  exact Finset.sum_le_sum fun j _ => (hB _ _ (hDm _) (hDN _)).2

end Analytic

section Up

open CategoryTheory AlgebraicGeometry Limits Set Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.ArchLim
open ReciprocityTheory.L2DbarEstimates (V)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem isEmbedding_up {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) [IsClosedImmersion j] (hj : j ≫ Z.s = q)
    (σ : c.F →+* ℂ) : IsEmbedding (up j hj σ) := by
  have h₁ : IsEmbedding fun y : CxPts q (σ.comp β) => y.1 ≫ j :=
    (isEmbedding_comp_of_isClosedImmersion (C := ℂ) j).comp IsEmbedding.subtypeVal
  have h₂ : Continuous fun x : CxPts (genStr Z) σ => x.1 ≫ genι Z :=
    (continuous_comp (genι Z)).comp continuous_subtype_val
  have e : (fun x : CxPts (genStr Z) σ => x.1 ≫ genι Z) ∘ up j hj σ = fun y => y.1 ≫ j :=
    funext fun y => up_ι j hj σ y
  refine ⟨IsInducing.of_comp (continuous_up j hj σ) h₂ (e ▸ h₁.isInducing), fun y y' h => ?_⟩
  have := congrArg (fun x : CxPts (genStr Z) σ => x.1 ≫ genι Z) h
  simp only [up_ι] at this
  exact h₁.injective this

theorem up_holo {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) [IsClosedImmersion j] (hj : j ≫ Z.s = q)
    (σ : c.F →+* ℂ) {D D' : ℕ} (ch : AlgChart q (σ.comp β) D) (c0 : AlgChart (genStr Z) σ D') {y : CxPts q (σ.comp β)}
    (hy : y ∈ ch.e.source) (hy0 : up j hj σ y ∈ c0.e.source) :
    (∀ᶠ v in 𝓝 (ch.e y), DifferentiableAt ℂ (c0.e ∘ up j hj σ ∘ ch.e.symm) v) ∧
      Function.Injective (fderiv ℂ (c0.e ∘ up j hj σ ∘ ch.e.symm) (ch.e y)) := by
  subst hj
  have P₁ := IsPullback.of_hasPullback j (genι Z)
  have P₂ : IsPullback (genι Z) (genStr Z) Z.s (spMap β) := IsPullback.of_hasPullback Z.s (spMap β)
  have HP := P₁.paste_vert P₂
  set i := pullback.snd j (genι Z)
  set bc := bcMap HP.w σ
  have hm : ∀ z, (bc z).1 = z.1 ≫ pullback.fst j (genι Z) := fun _ => rfl
  have hui : ∀ z, up j rfl σ (bc z) = PtsOver.map i rfl (spMap σ) z := fun z => by
    refine Subtype.ext (pullback.hom_ext ?_ ?_)
    · rw [up_ι]
      change (z.1 ≫ pullback.fst j (genι Z)) ≫ j = (z.1 ≫ i) ≫ genι Z
      rw [Category.assoc, Category.assoc, pullback.condition]
    · rw [(up j rfl σ (bc z)).2]
      exact z.2.symm
  obtain ⟨z, rfl⟩ := (bijective_bcMap HP σ).2 y
  obtain ⟨c', hz', hU, hx⟩ := ch.exists_baseChange HP hm hy
  have he : ∀ w, w ∈ c'.e.source → bc w ∈ ch.e.source → ch.e (bc w) = c'.e w := fun w h₁ h₂ => by
    ext a
    rw [ch.apply_eq _ h₂, c'.apply_eq _ h₁, hx, ev_appLE_of_comp hm hU _ (c'.source_subset h₁)]
  have hbc : Continuous bc := continuous_of_comp hm
  have hO : IsOpen (c'.e.target ∩ c'.e.symm ⁻¹' (bc ⁻¹' ch.e.source ∩ bc ⁻¹' (up j rfl σ ⁻¹' c0.e.source))) :=
    c'.e.isOpen_inter_preimage_symm ((ch.e.open_source.preimage hbc).inter
      ((c0.e.open_source.preimage (continuous_up j rfl σ)).preimage hbc))
  have hzO : c'.e z ∈ c'.e.target ∩ c'.e.symm ⁻¹' (bc ⁻¹' ch.e.source ∩ bc ⁻¹' (up j rfl σ ⁻¹' c0.e.source)) :=
    ⟨c'.e.map_source hz', by rw [mem_preimage, c'.e.left_inv hz']; exact ⟨hy, hy0⟩⟩
  have hsymm : ∀ v ∈ c'.e.target ∩ c'.e.symm ⁻¹' (bc ⁻¹' ch.e.source ∩ bc ⁻¹' (up j rfl σ ⁻¹' c0.e.source)),
      ch.e.symm v = bc (c'.e.symm v) := fun v hv => by
    have := he _ (c'.e.map_target hv.1) hv.2.1
    rw [c'.e.right_inv hv.1] at this
    conv_lhs => rw [← this]
    exact ch.e.left_inv hv.2.1
  have hyz : ch.e (bc z) = c'.e z := he z hz' hy
  have hev : c0.e ∘ up j rfl σ ∘ ch.e.symm =ᶠ[𝓝 (c'.e z)] c0.e ∘ PtsOver.map i rfl (spMap σ) ∘ c'.e.symm := by
    filter_upwards [hO.mem_nhds hzO] with v hv
    simp only [Function.comp_apply, hsymm v hv, hui]
  have hdiff := AlgChart.holo_map (f := i) (m := PtsOver.map i rfl (spMap σ)) (fun _ => rfl) c' c0
  have hO' : IsOpen (c'.e.target ∩ c'.e.symm ⁻¹' (PtsOver.map i rfl (spMap σ) ⁻¹' c0.e.source)) :=
    c'.e.isOpen_inter_preimage_symm (c0.e.open_source.preimage (PtsOver.continuous_map i rfl (spMap σ)))
  rw [hyz]
  refine ⟨?_, ?_⟩
  · filter_upwards [hev.eventuallyEq_nhds, hO.mem_nhds hzO] with v hv hv'
    refine (hdiff.differentiableAt (hO'.mem_nhds ⟨hv'.1, ?_⟩)).congr_of_eventuallyEq hv
    show PtsOver.map i rfl (spMap σ) (c'.e.symm v) ∈ c0.e.source
    rw [← hui]
    exact hv'.2.2
  · rw [hev.fderiv_eq]
    have := GlobalTheory.ImmInj.fderiv_injective c.F _ _ _ _ _ _ i inferInstance rfl σ c' c0 z hz' (by rw [← hui]; exact hy0)
    exact this

end Up

section Main

open CategoryTheory AlgebraicGeometry Limits Set Filter Topology NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.ArchLim GlobalTheory.FinChart GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V cHess)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor
open scoped ENNReal

theorem glueMeas_eq_zero {n : ℕ} {M ι : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (e : ι → OpenPartialHomeomorph M (V n)) (ρ : ι → M → ℝ≥0∞) {F : Set M} (hF : MeasurableSet F)
    (h0 : ∀ i, ∀ y ∈ (e i).source ∩ F, ρ i y = 0) : glueMeas e ρ F = 0 := by
  have hc : ∀ i, chartMeas (e i) (ρ i) F = 0 := fun i => by
    rw [chartMeas_apply (e i) (ρ i) hF]
    refine (setLIntegral_congr_fun (measurableSet_image _ ((e i).open_source.measurableSet.inter hF)
      inter_subset_left) ?_).trans (lintegral_zero)
    rintro _ ⟨y, hy, rfl⟩
    show ρ i ((e i).symm (e i y)) = 0
    rw [(e i).left_inv hy.1, h0 i y hy]
  have hle : glueMeas e ρ ≤ (glueMeas e ρ).restrict Fᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB]
    calc chartMeas (e i) (ρ i) B ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
          measure_mono fun y hy => by
            by_cases h : y ∈ F
            · exact Or.inr h
            · exact Or.inl ⟨hy, h⟩
      _ ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ) + chartMeas (e i) (ρ i) F := measure_union_le _ _
      _ = chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [hc i, add_zero]
      _ ≤ glueMeas e ρ (B ∩ Fᶜ) := Measure.le_iff'.1 (le_iSup (fun i => chartMeas (e i) (ρ i)) i) _
  have h := Measure.le_iff'.1 hle F
  rw [Measure.restrict_apply hF, inter_compl_self, measure_empty] at h
  exact nonpos_iff_eq_zero.1 h

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {τ : k →+* ℂ} {n : ℕ}

theorem setLIntegral_part_le [SecondCountableTopology (CxPts q τ)] {ρ : AlgChart q τ n → CxPts q τ → ℝ}
    (hρ : IsMDens ρ) (ch : AlgChart q τ n) {B : Set (CxPts q τ)} (hB : MeasurableSet B) (hBs : B ⊆ ch.e.source)
    (F : CxPts q τ → ℝ≥0∞) : MeasurableSet (ch.finChart '' B) ∧
      ∫⁻ x in B, F x ∂GlobalTheory.MixDens.part ρ ≤
        ∫⁻ z in ch.finChart '' B, ENNReal.ofReal (ρ ch (ch.finChart.symm z)) * F (ch.finChart.symm z) := by
  have hpre : ch.finChart '' B = toV n ⁻¹' (ch.e '' B) := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨x, hx, (toV n).injective (by rw [ch.toV_finChart]; exact h)⟩
  have hm := measurableSet_image ch.e hB hBs
  refine ⟨hpre ▸ hm.preimage (toV n).continuous.measurable, ?_⟩
  set g : CxPts q τ → ℝ≥0∞ := fun y => ENNReal.ofReal (ρ ch y)
  have hpart : (GlobalTheory.MixDens.part ρ).restrict B = (chartMeas ch.e g).restrict B := by
    ext T hT
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT]
    unfold GlobalTheory.MixDens.part
    exact glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
      rw [hρ.1 c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) ch (hT.inter hB) (inter_subset_right.trans hBs)
  have hT := ch.e.open_target.measurableSet
  have hgm : AEMeasurable (g ∘ ch.e.symm) (volume.restrict ch.e.target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hρ.2 ch)
  calc ∫⁻ x in B, F x ∂GlobalTheory.MixDens.part ρ = ∫⁻ x, B.indicator F x ∂chartMeas ch.e g := by
        rw [hpart, lintegral_indicator hB]
    _ ≤ ∫⁻ v, B.indicator F (ch.e.symm v) ∂(volume.restrict ch.e.target).withDensity (g ∘ ch.e.symm) :=
        lintegral_map_le _ _
    _ = ∫⁻ v in ch.e.target, (g ∘ ch.e.symm) v * B.indicator F (ch.e.symm v) := by
        rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hgm
          (.of_forall fun _ => ENNReal.ofReal_lt_top)]
        rfl
    _ ≤ ∫⁻ v in ch.e.target, (ch.e '' B).indicator (fun v => g (ch.e.symm v) * F (ch.e.symm v)) v := by
        refine setLIntegral_mono' hT fun v hv => ?_
        by_cases h : ch.e.symm v ∈ B
        · have : v ∈ ch.e '' B := ⟨_, h, ch.e.right_inv hv⟩
          simp [indicator_of_mem h, indicator_of_mem this]
        · simp [indicator_of_notMem h]
    _ ≤ ∫⁻ v, (ch.e '' B).indicator (fun v => g (ch.e.symm v) * F (ch.e.symm v)) v := setLIntegral_le_lintegral _ _
    _ = ∫⁻ v in ch.e '' B, g (ch.e.symm v) * F (ch.e.symm v) := lintegral_indicator hm _
    _ = _ := by
        rw [hpre]
        exact (measurePreserving_toV.setLIntegral_comp_preimage_emb (toV n).toHomeomorph.measurableEmbedding
          (fun v => g (ch.e.symm v) * F (ch.e.symm v)) _).symm

theorem paramDens_eq_potDens {X : Type} [TopologicalSpace X] {d : ℕ} {P : LocPot X} {S : Set X}
    {u : CxPts q τ → X} (ch : AlgChart q τ n) {ψ : OpenPartialHomeomorph X (Fin d → ℂ)} {N : Set (CxPts q τ)}
    (hN : IsOpen N) (hψ : ∀ x ∈ N, u x ∈ ψ.source ∧ ψ (u x) = padZero n d (ch.finChart x)) {x : CxPts q τ}
    (hxN : x ∈ N) (hx : x ∈ ch.e.source) (hxS : u x ∈ S)
    (hC : ContDiffAt ℝ 2 (fun v => P.φ (u x) (u (ch.e.symm v))) (ch.e x)) :
    paramDens n P ψ (ch.finChart x) = potDens P S u ch x := by
  have hpar : ∀ x' ∈ N, param n ψ (ch.finChart x') = u x' := fun x' hx' => by
    rw [param, ← (hψ x' hx').2, ψ.left_inv (hψ x' hx').1]
  have hO : IsOpen (ch.finChart.target ∩ ch.finChart.symm ⁻¹' N) := ch.finChart.isOpen_inter_preimage_symm hN
  have hxO : ch.finChart x ∈ ch.finChart.target ∩ ch.finChart.symm ⁻¹' N :=
    ⟨ch.finChart.map_source hx, by rw [mem_preimage, ch.finChart.left_inv hx]; exact hxN⟩
  have hev : (fun z' => P.φ (u x) (param n ψ z')) =ᶠ[𝓝 (ch.finChart x)]
      (fun v => P.φ (u x) (u (ch.e.symm v))) ∘ toV n := by
    filter_upwards [hO.mem_nhds hxO] with z' hz'
    have := hpar _ hz'.2
    rw [ch.finChart.right_inv hz'.1] at this
    simp only [Function.comp_apply, this]
    rfl
  unfold paramDens
  rw [hpar x hxN, maDens_congr_eventuallyEq (fun _ => hev), maDens, ReciprocityTheory.AnForm.A.mdisc_const, potDens,
    if_pos hxS, potMat, ← ch.toV_finChart x, cHess_eq_hessC (by rwa [ch.toV_finChart])]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem up_fin {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) [IsClosedImmersion j] (hj : j ≫ Z.s = q)
    (σ : c.F →+* ℂ) {D D' : ℕ} (ch : AlgChart q (σ.comp β) D) (c0 : AlgChart (genStr Z) σ D') {y : CxPts q (σ.comp β)}
    (hy : y ∈ ch.e.source) (hy0 : up j hj σ y ∈ c0.e.source) :
    AnalyticAt ℂ (c0.e ∘ up j hj σ ∘ ch.e.symm) (ch.e y) ∧
      AnalyticAt ℂ (c0.finChart ∘ up j hj σ ∘ ch.finChart.symm) (ch.finChart y) ∧
      Function.Injective (fderiv ℂ (c0.finChart ∘ up j hj σ ∘ ch.finChart.symm) (ch.finChart y)) := by
  obtain ⟨hd, hinj⟩ := up_holo j hj σ ch c0 hy hy0
  obtain ⟨s, hs, hsd⟩ := Filter.eventually_iff_exists_mem.1 hd
  have hdo : DifferentiableOn ℂ (c0.e ∘ up j hj σ ∘ ch.e.symm) s := fun v hv => (hsd v hv).differentiableWithinAt
  have han : AnalyticAt ℂ (c0.e ∘ up j hj σ ∘ ch.e.symm) (ch.e y) := by
    obtain ⟨t, hts, ht, hyt⟩ := mem_nhds_iff.1 hs
    exact (SCV.analyticOnNhd_iff_differentiableOn ht).2 (hdo.mono hts) _ hyt
  set E1 := EuclideanSpace.equiv (Fin D) ℂ
  set E0 := EuclideanSpace.equiv (Fin D') ℂ
  have hfun : c0.finChart ∘ up j hj σ ∘ ch.finChart.symm = E0 ∘ (c0.e ∘ up j hj σ ∘ ch.e.symm) ∘ E1.symm := rfl
  have hpt : ch.finChart y = E1 (ch.e y) := rfl
  refine ⟨han, ?_, ?_⟩
  · rw [hfun, hpt]
    exact ((E0 : V D' →L[ℂ] (Fin D' → ℂ)).analyticAt _).comp
      (AnalyticAt.comp_of_eq han ((E1.symm : (Fin D → ℂ) →L[ℂ] V D).analyticAt _) (E1.symm_apply_apply _))
  · rw [hfun, hpt, E0.comp_fderiv, E1.symm.comp_right_fderiv, E1.symm_apply_apply]
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hab
    exact E1.symm.injective (hinj (E0.injective hab))

theorem contDiffAt_pull {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) [IsClosedImmersion j] (hj : j ≫ Z.s = q)
    (σ : c.F →+* ℂ) {D D' : ℕ} {A : FinHolAtlas D' (CxPts (genStr Z) σ)} (hA : IsAlgAtlas A)
    (ch : AlgChart q (σ.comp β) D) {x : CxPts q (σ.comp β)} (hx : x ∈ ch.e.source) {g : CxPts (genStr Z) σ → ℝ}
    {W : Set (CxPts (genStr Z) σ)} (hW : IsOpen W) (hxW : up j hj σ x ∈ W) (hg : A.SmoothOn W g) :
    ContDiffAt ℝ 2 (fun v => g (up j hj σ (ch.e.symm v))) (ch.e x) := by
  obtain ⟨kk, hk⟩ := A.cover (up j hj σ x)
  obtain ⟨c0, hc0⟩ := hA kk
  have hk0 : up j hj σ x ∈ c0.e.source := by rw [hc0] at hk; exact hk
  have hg1 : ContDiffAt ℝ 2 (g ∘ (A.chart kk).symm) (A.chart kk (up j hj σ x)) :=
    ((hg kk).contDiffAt (((A.chart kk).isOpen_inter_preimage_symm hW).mem_nhds
      ⟨(A.chart kk).map_source hk, by rw [mem_preimage, (A.chart kk).left_inv hk]; exact hxW⟩)).of_le
      (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)
  have han := (up_fin j hj σ ch c0 hx hk0).1
  have hg2 : ContDiffAt ℝ 2 (A.chart kk ∘ up j hj σ ∘ ch.e.symm) (ch.e x) := by
    rw [hc0]
    exact ((((EuclideanSpace.equiv (Fin D') ℂ : V D' →L[ℂ] (Fin D' → ℂ)).analyticAt _).comp han).contDiffAt).restrict_scalars ℝ
  have hO : IsOpen (ch.e.target ∩ ch.e.symm ⁻¹' (up j hj σ ⁻¹' (A.chart kk).source)) :=
    ch.e.isOpen_inter_preimage_symm ((A.chart kk).open_source.preimage (continuous_up j hj σ))
  have heq : (A.chart kk ∘ up j hj σ ∘ ch.e.symm) (ch.e x) = A.chart kk (up j hj σ x) := by
    simp only [Function.comp_apply, ch.e.left_inv hx]
  rw [← heq] at hg1
  refine (hg1.comp (ch.e x) hg2).congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds ⟨ch.e.map_source hx, by rw [mem_preimage, ch.e.left_inv hx]; exact hk⟩] with v hv
  simp only [Function.comp_apply, (A.chart kk).left_inv hv.2]

end Main

section Final

open CategoryTheory AlgebraicGeometry Limits Set Filter Topology NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.ArchLim GlobalTheory.FinChart GlobalTheory.ChartGlue
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem lintegral_up_le {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp Oz} (jm : Y ⟶ Z.X) [IsClosedImmersion jm]
    (hq : jm ≫ Z.s = q) (σ : c.F →+* ℂ) {D' : ℕ} (R : AnRead (genStr Z) σ D') [CompactSpace (CxPts (genStr Z) σ)]
    (n : ℕ) (hY : IsArithVar q n) (m : ℕ) (Zs : Fin m → Set (CxPts (genStr Z) σ)) (T₀ : Set Y) (hT₀ : IsClosed T₀)
    (hgen : genericPoint Y ∉ T₀)
    (hZs : ∀ y : CxPts q (σ.comp β), y.1 (IsLocalRing.closedPoint ℂ) ∉ T₀ →
      ∃ a W, IsOpen W ∧ up jm hq σ y ∈ W ∧ W ∩ Set.range (up jm hq σ) = W ∩ Zs a)
    (P : LocPot (CxPts (genStr Z) σ)) (Bd : Set (CxPts (genStr Z) σ)) (hBd : IsClosed Bd)
    (hP : ∀ y, y ∉ Bd → ∃ W, IsOpen W ∧ y ∈ W ∧ W ⊆ P.U y ∧ R.finAtlas.SmoothOn W (P.φ y))
    (hρ : IsMDens (D := n) (potDens P Bdᶜ (up jm hq σ))) (f : CxPts (genStr Z) σ → ℝ≥0∞) :
    ∫⁻ y, f (up jm hq σ y) ∂GlobalTheory.MixDens.part (D := n) (potDens P Bdᶜ (up jm hq σ)) ≤
      ∑ a, regIntegral R.finAtlas (Zs a) n P (regularLocus R.finAtlas (Zs a) n \ Bd) f := by
  haveI : SecondCountableTopology (CxPts q (σ.comp β)) :=
    CxPts.secondCountableTopology_of_isProjOver _ hY.isProjOver
  have hA : IsAlgAtlas R.finAtlas := R.isAlgAtlas_finAtlas
  have hemb := isEmbedding_up jm hq σ
  have hu := continuous_up jm hq σ
  set u := up jm hq σ with hudef
  set ρ : AlgChart q (σ.comp β) n → CxPts q (σ.comp β) → ℝ := potDens P Bdᶜ u with hρdef
  set Cs : Set (CxPts q (σ.comp β)) := {x | ∃ ch : AlgChart q (σ.comp β) n, x ∈ ch.e.source} with hCsdef
  have hCs : IsOpen Cs := by
    have : Cs = ⋃ ch : AlgChart q (σ.comp β) n, ch.e.source := by
      ext x
      simp [Cs]
    rw [this]
    exact isOpen_iUnion fun ch => ch.e.open_source
  set G := {x : CxPts q (σ.comp β) | x.1 (IsLocalRing.closedPoint ℂ) ∉ T₀} ∩ (Cs ∩ u ⁻¹' Bdᶜ) with hGdef
  have hF : MeasurableSet (Cs ∩ u ⁻¹' Bdᶜ)ᶜ := (hCs.inter (hBd.isOpen_compl.preimage hu)).measurableSet.compl
  have hF0 : GlobalTheory.MixDens.part ρ (Cs ∩ u ⁻¹' Bdᶜ)ᶜ = 0 := by
    unfold GlobalTheory.MixDens.part
    refine glueMeas_eq_zero _ _ hF fun ch x hx => ?_
    have : u x ∈ Bd := by
      by_contra h
      exact hx.2 ⟨⟨ch, hx.1⟩, h⟩
    simp [hρdef, potDens, this]
  have hT0 := GlobalTheory.MixDensNull.part_over_closed Oz Y q n hY T₀ hT₀ hgen (σ.comp β) ρ
  have hG : GlobalTheory.MixDens.part ρ Gᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hT0 hF0)
    by_cases h : x.1 (IsLocalRing.closedPoint ℂ) ∈ T₀
    · exact Or.inl h
    · exact Or.inr fun h' => hx ⟨h, h'⟩
  refine lintegral_le_sum R.finAtlas Zs (fun a => regularLocus R.finAtlas (Zs a) n \ Bd) P f _ hemb.injective hG ?_
  rintro y ⟨hyT, ⟨ch, hyc⟩, hyBd⟩
  obtain ⟨a, W, hW, hyW, hZW⟩ := hZs y hyT
  obtain ⟨kk, hk⟩ := R.finAtlas.cover (u y)
  obtain ⟨c0, hc0⟩ := hA kk
  have hk0 : u y ∈ c0.e.source := by rw [hc0] at hk; exact hk
  obtain ⟨-, hanF, hinjF⟩ := up_fin jm hq σ ch c0 hyc hk0
  obtain ⟨ψ, hψ, hyψ, hkey⟩ := exists_straightening R.finAtlas hemb.isInducing ch.finChart hyc c0.finChart
    (hA.isCompatChart c0) hk0 hanF hinjF hW hyW hZW
  have hNo : IsOpen (u ⁻¹' ψ.source ∩ u ⁻¹' Bdᶜ) := (ψ.open_source.preimage hu).inter (hBd.isOpen_compl.preimage hu)
  have hpar : ∀ x, u x ∈ ψ.source → param n ψ (ch.finChart x) = u x := fun x hx => by
    rw [param, ← (hkey x hx).2.2, ψ.left_inv hx]
  refine ⟨_, hNo, ⟨hyψ, hyBd⟩, a, ψ, ch.finChart, hψ,
    fun x hx => ⟨?_, hpar x hx.1, ⟨(hkey x hx.1).2.1, ψ, hψ, hx.1⟩, hx.2⟩, fun B hB hBN => ?_⟩
  · rw [← (hkey x hx.1).2.2]
    exact ψ.map_source hx.1
  have hBs : B ⊆ ch.e.source := fun x hx => (hkey x (hBN hx).1).1
  obtain ⟨hm, hle⟩ := setLIntegral_part_le hρ ch hB hBs (fun x => f (u x))
  refine ⟨hm, hle.trans (setLIntegral_mono' hm ?_)⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxs := hBs hx
  obtain ⟨hxψ, hxBd⟩ := hBN hx
  obtain ⟨W', hW', hxW', -, hsm⟩ := hP (u x) hxBd
  have hC := contDiffAt_pull jm hq σ hA ch hxs hW' hxW' hsm
  have hd := paramDens_eq_potDens (P := P) (S := Bdᶜ) ch (ψ := ψ) (N := u ⁻¹' ψ.source) (ψ.open_source.preimage hu)
    (fun x' hx' => ⟨hx', (hkey x' hx').2.2⟩) hxψ hxs hxBd hC
  rw [ch.finChart.left_inv hxs, hpar x hxψ, hd, mul_comm (f (u x))]
  gcongr
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans_eq (Real.enorm_eq_ofReal_abs _).symm

end Final

end GlobalTheory.UpMeas

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

theorem GlobalTheory.UpMeas.lintegral_up_le_regIntegral : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp _) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → ∀ (m : ℕ) (Zs : Fin m → Set (CxPts (genStr s.T.Z) σ)) (T₀ : Set Y), IsClosed T₀ → genericPoint Y ∉ T₀ → (∀ y : CxPts q (σ.comp _), y.1 (IsLocalRing.closedPoint ℂ) ∉ T₀ → ∃ a W, IsOpen W ∧ up jm hq σ y ∈ W ∧ W ∩ Set.range (up jm hq σ) = W ∩ Zs a) → ∀ (P : LocPot (CxPts (genStr s.T.Z) σ)) (Bd : Set (CxPts (genStr s.T.Z) σ)), IsClosed Bd → (∀ y, y ∉ Bd → ∃ W, IsOpen W ∧ y ∈ W ∧ W ⊆ P.U y ∧ ((manifold s.T.Z σ).finAtlas).SmoothOn W (P.φ y)) → IsMDens (D := n) (potDens P Bdᶜ (up jm hq σ)) → ∀ f : CxPts (genStr s.T.Z) σ → ℝ≥0∞, ∫⁻ y, f (up jm hq σ y) ∂part (D := n) (potDens P Bdᶜ (up jm hq σ)) ≤ ∑ a, regIntegral (manifold s.T.Z σ).finAtlas (Zs a) n P (regularLocus (manifold s.T.Z σ).finAtlas (Zs a) n \ Bd) f := by
  intro D A N j S κ s σ _ Y _ q jm _ hq n hY m Zs T₀ hT₀ hgen hZs P Bd hBd hP hρ f
  exact GlobalTheory.UpMeas.lintegral_up_le jm hq σ (manifold s.T.Z σ) n hY m Zs T₀ hT₀ hgen hZs P Bd hBd hP hρ f
