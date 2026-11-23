import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperSheetedFibreEsymm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametricCircleIntegralAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set Complex

open scoped Real

namespace ProperSheetedFibreEsymm

open Classical in

noncomputable def fibreEsymm {σ : Type} {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ) (t : Fin d → ℂ) : ℂ :=
  if h : {x | x ∈ Y ∧ A x = t}.Finite then (h.toFinset.val.map l).esymm j else 0

theorem fibreEsymm_eq {σ : Type} {d : ℕ} {Y : Set (σ → ℂ)} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {l : (σ → ℂ) →L[ℂ] ℂ} {j : ℕ} {t : Fin d → ℂ} (s : Finset (σ → ℂ))
    (hs : (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = t}) : fibreEsymm Y A l j t = (s.val.map l).esymm j := by
  have h : {x | x ∈ Y ∧ A x = t}.Finite := hs ▸ s.finite_toSet
  have hs' : h.toFinset = s := Finset.coe_injective (by rw [Set.Finite.coe_toFinset, hs])
  rw [fibreEsymm, dif_pos h, hs']

theorem fibre_sections {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (hD : IsOpen D)
    (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {y : Fin d → ℂ} (hyD : y ∈ D) (hδy : δ y ≠ 0) :
    ∃ (F : Finset (σ → ℂ)) (g : (σ → ℂ) → (Fin d → ℂ) → σ → ℂ), (∀ x ∈ F, AnalyticAt ℂ (g x) y) ∧
      ∀ᶠ y' in 𝓝 y, Set.InjOn (fun x => g x y') ↑F ∧
        {x | x ∈ Y ∧ A x = y'} = (fun x => g x y') '' ↑F := by
  choose! O V g hO hV hxV hg hsec hYV using hchart

  have key : ∀ x ∈ Y, δ (A x) ≠ 0 → ∀ z ∈ Y, z ∈ V x → A z ∈ O x ∧ g x (A z) = z := by
    intro x hx hδ z hz hzV
    obtain ⟨w, hw, rfl⟩ : z ∈ g x '' O x := hYV x hx hδ ▸ ⟨hz, hzV⟩
    rw [hsec x hx hδ w hw]; exact ⟨hw, rfl⟩
  set F := {x | x ∈ Y ∧ A x = y} with hFdef
  have hFδ : ∀ x ∈ F, δ (A x) ≠ 0 := fun x hx => hx.2 ▸ hδy
  have hyO : ∀ x ∈ F, y ∈ O x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).1
  have hgy : ∀ x ∈ F, g x y = x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).2

  have hFc : IsCompact F := by
    simpa [hFdef] using hprop {y} (singleton_subset_iff.2 hyD) isCompact_singleton
  have hFfin : F.Finite := by
    obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover V
      (fun x hx => (hV x hx.1 (hFδ x hx)).mem_nhds (hxV x hx.1 (hFδ x hx)))
    refine t.finite_toSet.subset fun z hz => ?_
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hz)
    have hx := htF x hxt
    have := (key x hx.1 (hFδ x hx) z hz.1 hzx).2
    rw [hz.2, hgy x hx] at this
    exact this ▸ hxt
  refine ⟨hFfin.toFinset, g, fun x hx => ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset] at hx
    exact hg x hx.1 (hFδ x hx) y (hyO x hx)
  rw [Set.Finite.coe_toFinset]

  have hev1 : ∀ᶠ y' in 𝓝 y, ∀ x ∈ F, y' ∈ O x :=
    (eventually_all_finite hFfin).2 fun x hx => (hO x hx.1 (hFδ x hx)).mem_nhds (hyO x hx)

  have hev2 : ∀ᶠ y' in 𝓝 y, ∀ p ∈ F ×ˢ F, p.1 ≠ p.2 → g p.1 y' ≠ g p.2 y' := by
    refine (eventually_all_finite (hFfin.prod hFfin)).2 fun p hp => ?_
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    have c1 := (hg p.1 hp.1.1 (hFδ _ hp.1) y (hyO _ hp.1)).continuousAt
    have c2 := (hg p.2 hp.2.1 (hFδ _ hp.2) y (hyO _ hp.2)).continuousAt
    have hne' : g p.1 y ≠ g p.2 y := by rwa [hgy _ hp.1, hgy _ hp.2]
    exact ((c1.tendsto.prodMk_nhds c2.tendsto).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hne')).mono fun _ h _ => h

  have hev3 : ∀ᶠ y' in 𝓝 y, ∀ z ∈ Y, A z = y' → ∃ x ∈ F, z ∈ V x := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD y hyD
    set K := Metric.closedBall y (ε / 2)
    have hKD : K ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
    set W := ⋃ x ∈ F, V x
    have hW : IsOpen W := isOpen_biUnion fun x hx => hV x hx.1 (hFδ x hx)
    have hC : IsCompact ({z | z ∈ Y ∧ A z ∈ K} \ W) :=
      (hprop K hKD (isCompact_closedBall y _)).diff hW
    have hyn : y ∉ A '' ({z | z ∈ Y ∧ A z ∈ K} \ W) := by
      rintro ⟨z, ⟨⟨hzY, -⟩, hzW⟩, hzy⟩
      exact hzW (mem_iUnion₂.2 ⟨z, ⟨hzY, hzy⟩, hxV z hzY (hzy ▸ hδy)⟩)
    filter_upwards [Metric.closedBall_mem_nhds y (half_pos hε),
      (hC.image A.continuous).isClosed.isOpen_compl.mem_nhds hyn] with y' hy'K hy'C z hzY hzy
    by_contra hno
    exact hy'C ⟨z, ⟨⟨hzY, hzy ▸ hy'K⟩, fun h => hno (by simpa [W] using h)⟩, hzy⟩
  filter_upwards [hev1, hev2, hev3] with y' h1 h2 h3
  refine ⟨fun a ha b hb hab => ?_, ?_⟩
  · by_contra hne
    exact h2 (a, b) ⟨ha, hb⟩ hne hab
  ext z
  constructor
  · rintro ⟨hzY, hzy⟩
    obtain ⟨x, hx, hzx⟩ := h3 z hzY hzy
    exact ⟨x, hx, by simpa [hzy] using (key x hx.1 (hFδ x hx) z hzY hzx).2⟩
  · rintro ⟨x, hx, rfl⟩
    have hm : g x y' ∈ Y ∩ V x := hYV x hx.1 (hFδ x hx) ▸ mem_image_of_mem _ (h1 x hx)
    exact ⟨hm.1, hsec x hx.1 (hFδ x hx) y' (h1 x hx)⟩

theorem fibreEsymm_analyticAt {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ)
    (hD : IsOpen D) (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {y : Fin d → ℂ} (hyD : y ∈ D) (hδy : δ y ≠ 0) : AnalyticAt ℂ (fibreEsymm Y A l j) y := by
  classical
  obtain ⟨F, g, hga, hev⟩ := fibre_sections hD hprop hchart hyD hδy
  have hP : AnalyticAt ℂ (fun t => ∑ u ∈ F.powersetCard j, ∏ x ∈ u, l (g x t)) y :=
    Finset.analyticAt_fun_sum _ fun u hu => Finset.analyticAt_fun_prod _ fun x hx =>
      (l.analyticAt _).comp (hga x ((Finset.mem_powersetCard.1 hu).1 hx))
  refine hP.congr ?_
  filter_upwards [hev] with t ht
  rw [fibreEsymm_eq (F.image fun x => g x t) (by rw [Finset.coe_image, ht.2]),
    Finset.image_val_of_injOn ht.1, Multiset.map_map, Finset.esymm_map_val]
  rfl

theorem norm_esymm_map_le {ι : Type*} (S : Finset ι) (f : ι → ℂ) (j : ℕ) {C : ℝ} (hC : ∀ x ∈ S, ‖f x‖ ≤ C) :
    ‖(S.val.map f).esymm j‖ ≤ (S.card.choose j : ℝ) * C ^ j := by
  rw [Finset.esymm_map_val]
  calc ‖∑ u ∈ S.powersetCard j, ∏ x ∈ u, f x‖ ≤ ∑ u ∈ S.powersetCard j, ‖∏ x ∈ u, f x‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S.powersetCard j, C ^ j := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨hu1, hu2⟩ := Finset.mem_powersetCard.1 hu
        rw [norm_prod, ← hu2, ← Finset.prod_const]
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun x hx => hC x (hu1 hx)
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

theorem fibreEsymm_locally_bounded (hcount : UnbranchedProperCountConstant.Statement) {σ : Type} [Fintype σ]
    {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ) (hD : IsOpen D)
    (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) (hδ : AnalyticOnNhd ℂ δ D)
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {τ : Fin d → ℂ} (hτ : τ ∈ D) :
    ∃ N ∈ 𝓝 τ, Bornology.IsBounded (fibreEsymm Y A l j '' (N ∩ D ∩ {t | δ t ≠ 0})) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD τ hτ
  set B := Metric.ball τ (ε / 2)
  have hKD : Metric.closedBall τ (ε / 2) ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBD : B ⊆ D := Metric.ball_subset_closedBall.trans hKD

  obtain ⟨n, hn⟩ := hcount σ (Y ∩ A ⁻¹' B) d A B δ Metric.isOpen_ball (convex_ball τ _).isPreconnected
    (fun x hx => hx.2) (fun K hK hKc => by
      convert hprop K (hK.trans hBD) hKc using 1
      ext x; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hK h.2⟩, h.2⟩⟩) (hδ.mono hBD) (by
      intro x hx hδx
      obtain ⟨O, V, g, hO, hV, hxV, hg, hsec, hYV⟩ := hchart x hx.1 hδx
      refine ⟨O ∩ B, V, g, hO.inter Metric.isOpen_ball, hV, hxV, hg.continuousOn.mono inter_subset_left,
        fun y hy => hsec y hy.1, ?_⟩
      ext z
      constructor
      · rintro ⟨⟨hzY, hzB⟩, hzV⟩
        obtain ⟨w, hw, rfl⟩ : z ∈ g '' O := hYV ▸ ⟨hzY, hzV⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        have : A (g w) ∈ B := hzB
        rwa [hsec w hw] at this
      · rintro ⟨w, ⟨hw, hwB⟩, rfl⟩
        have hm : g w ∈ Y ∩ V := hYV ▸ mem_image_of_mem g hw
        refine ⟨⟨hm.1, ?_⟩, hm.2⟩
        show A (g w) ∈ B
        rwa [hsec w hw])

  obtain ⟨C, hC⟩ := (hprop _ hKD (isCompact_closedBall τ _)).exists_bound_of_continuousOn
    l.continuous.continuousOn
  refine ⟨B, Metric.ball_mem_nhds τ (half_pos hε), (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨(n.choose j : ℝ) * C ^ j, ?_⟩⟩
  rintro _ ⟨t, ⟨⟨htB, -⟩, htδ⟩, rfl⟩
  have hfib : {x | x ∈ Y ∩ A ⁻¹' B ∧ A x = t} = {x | x ∈ Y ∧ A x = t} := by
    ext x; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, show A x ∈ B from h.2 ▸ htB⟩, h.2⟩⟩
  have hcard := hn t htB htδ
  rw [hfib] at hcard
  have hfin : {x | x ∈ Y ∧ A x = t}.Finite := Set.finite_of_encard_eq_coe hcard
  rw [hfin.encard_eq_coe_toFinset_card, Nat.cast_inj] at hcard
  rw [Metric.mem_closedBall, dist_zero_right, fibreEsymm_eq hfin.toFinset hfin.coe_toFinset, ← hcard]
  refine norm_esymm_map_le _ _ _ fun x hx => hC x ?_
  rw [Set.Finite.mem_toFinset] at hx
  exact ⟨hx.1, hx.2 ▸ Metric.ball_subset_closedBall htB⟩

theorem analyticOnNhd_of_differentiableOn (hcirc : ParametricCircleIntegralAnalytic.Statement) {k : ℕ}
    {U : Set (Fin k → ℂ)} {F : (Fin k → ℂ) → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := by
  have h := hcirc (Fin k) (fun p => F p.1 * p.2⁻¹) (U ×ˢ {s | s ≠ 0}) U 0 1 zero_le_one
    (hU.prod isOpen_ne) hU
    ((hF.comp differentiable_fst.differentiableOn fun p hp => hp.1).mul
      (differentiable_snd.differentiableOn.inv fun p hp => hp.2))
    (fun x hx s hs => ⟨hx, by rintro rfl; simp at hs⟩)
  have hinv : (∮ z in C(0, 1), z⁻¹) = 2 * π * I := by
    simpa using circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := 1) (by simp)
  intro x hx
  refine ((h x hx).mul (analyticAt_const (v := (2 * π * I)⁻¹))).congr (Eventually.of_forall fun y => ?_)
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [Pi.mul_apply, circleIntegral.integral_const_mul, hinv]
  field_simp

end ProperSheetedFibreEsymm

open ProperSheetedFibreEsymm in

theorem ProperSheetedFibreEsymm.proof (hcount : UnbranchedProperCountConstant.Statement)
    (hriem : RiemannExtensionAnalytic.Statement) (hcirc : ParametricCircleIntegralAnalytic.Statement) :
    ProperSheetedFibreEsymm.Statement := by
  intro σ _ Y d A D δ l j hD _ hprop hδ hW hchart
  obtain ⟨F, hFd, hFeq⟩ := hriem d D δ (fibreEsymm Y A l j) hD hδ.differentiableOn hW
    (fun t ht => (fibreEsymm_analyticAt l j hD hprop hchart ht.1 ht.2).differentiableAt.differentiableWithinAt)
    (fun τ hτ => fibreEsymm_locally_bounded hcount l j hD hprop hδ hchart hτ)
  refine ⟨F, analyticOnNhd_of_differentiableOn hcirc hD hFd, fun t ht hδt s hs => ?_⟩
  rw [hFeq ⟨ht, hδt⟩, fibreEsymm_eq s hs]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
