import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionOpenAt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCentredDiscCoverCurve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

namespace GlobalTheory.CompanionTheory.ComplexSets.DiscCover

open Metric

theorem const_coord (y : Fin 1 → ℂ) : (fun _ : Fin 1 => y 0) = y := by
  funext i
  rw [Subsingleton.elim i 0]

theorem line_ext {y y' : Fin 1 → ℂ} (h : y 0 = y' 0) : y = y' := by
  funext i
  rw [Subsingleton.elim i 0]
  exact h

theorem line_dist (y y' : Fin 1 → ℂ) : dist y y' = dist (y 0) (y' 0) := by
  have h : dist (fun _ : Fin 1 => y 0) (fun _ : Fin 1 => y' 0) = dist (y 0) (y' 0) :=
    dist_pi_const (y 0) (y' 0)
  rw [const_coord y, const_coord y'] at h
  exact h

theorem mem_line_ball {y c : Fin 1 → ℂ} {ρ : ℝ} : y ∈ ball c ρ ↔ y 0 ∈ ball (c 0) ρ := by
  simp only [mem_ball, line_dist]

theorem exists_punctured_ball_ne_zero (δ : (Fin 1 → ℂ) → ℂ) (c : Fin 1 → ℂ) (hδ : AnalyticAt ℂ δ c)
    (hne : ¬ ∀ᶠ y in 𝓝 c, δ y = 0) : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y ∈ ball c ρ₀, y ≠ c → δ y ≠ 0 := by
  set e := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hF : AnalyticAt ℂ (fun t : ℂ => δ (fun _ => t)) (c 0) := by
    have h1 : AnalyticAt ℂ δ (e.symm (c 0)) := by
      have h2 : e.symm (c 0) = c := const_coord c
      rw [h2]
      exact hδ
    exact h1.comp (e.symm.analyticAt _)
  rcases hF.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · exfalso
    apply hne
    have ht : Tendsto (fun y : Fin 1 → ℂ => y 0) (𝓝 c) (𝓝 (c 0)) := (continuous_apply 0).tendsto c
    filter_upwards [ht h0] with y hy
    have hy' : δ (fun _ => y 0) = 0 := hy
    rwa [const_coord] at hy'
  · obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h1)
    refine ⟨ε, hε, fun y hy hyc => ?_⟩
    have h2 := h (y := y 0) (by simpa [line_dist] using mem_ball.1 hy)
      (fun h3 => hyc (line_ext h3))
    rwa [const_coord] at h2

theorem isCompact_inter_of_cut {σ : Type} [Fintype σ] {Y C Nn : Set (σ → ℂ)} {k : ℕ}
    {f : Fin k → (σ → ℂ) → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) Nn)
    (hY : Y ∩ Nn = {z | z ∈ Nn ∧ ∀ i, f i z = 0}) (hC : IsCompact C) (hsub : C ⊆ Nn) :
    IsCompact (Y ∩ C) := by
  have hcont : ContinuousOn (fun z i => f i z) C :=
    continuousOn_pi.2 fun i => (hf i).continuousOn.mono hsub
  have hcl := hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := (0 : Fin k → ℂ)))
  have heq : Y ∩ C = C ∩ (fun z i => f i z) ⁻¹' {(0 : Fin k → ℂ)} := by
    ext z
    constructor
    · rintro ⟨hzY, hzC⟩
      have h : z ∈ Y ∩ Nn := ⟨hzY, hsub hzC⟩
      rw [hY] at h
      exact ⟨hzC, funext h.2⟩
    · rintro ⟨hzC, hz⟩
      have h : z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0} := ⟨hsub hzC, fun i => congrFun hz i⟩
      rw [← hY] at h
      exact ⟨h.1, hzC⟩
  rw [heq]
  exact hC.of_isClosed_subset hcl Set.inter_subset_left

theorem cover_of_radii (hCount : UnbranchedProperCountConstant.Statement) (σ : Type) [Fintype σ]
    (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (hw : w ∈ Y) (hcomp : IsCompact (Y ∩ closedBall w r))
    (hsph : ∀ x ∈ Y, dist x w = r → A x ∉ ball (A w) ρ)
    (hiso : ∀ x ∈ Y ∩ closedBall w r, A x = A w → x = w)
    (hsheet : ∀ x ∈ Y ∩ closedBall w r, A x ≠ A w → A x ∈ ball (A w) ρ →
      ∃ (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
        AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ Y ∩ V = g '' O)
    (hsurj : A '' (Y ∩ ball w r) ∈ 𝓝 (A w)) :
    ∃ N : ℕ, IsCentredDiscCover (Y ∩ (ball w r ∩ A ⁻¹' ball (A w) ρ)) w
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp A) ρ N := by
  set B := ball w r ∩ A ⁻¹' ball (A w) ρ with hBdef
  have hBopen : IsOpen B := isOpen_ball.inter (isOpen_ball.preimage A.continuous)
  have hclosed : ∀ C : Set (Fin 1 → ℂ), IsClosed C → C ⊆ ball (A w) ρ →
      IsCompact {x | x ∈ Y ∩ B ∧ A x ∈ C} := by
    intro C hC hCD
    have heq : {x | x ∈ Y ∩ B ∧ A x ∈ C} = (Y ∩ closedBall w r) ∩ A ⁻¹' C := by
      ext x
      constructor
      · rintro ⟨⟨hxY, hxb, -⟩, hxC⟩
        exact ⟨⟨hxY, ball_subset_closedBall hxb⟩, hxC⟩
      · rintro ⟨⟨hxY, hxb⟩, hxC⟩
        have hD := hCD hxC
        refine ⟨⟨hxY, ?_, hD⟩, hxC⟩
        rcases (mem_closedBall.1 hxb).lt_or_eq with h | h
        · exact mem_ball.2 h
        · exact absurd hD (hsph x hxY h)
    rw [heq]
    exact hcomp.inter_right (hC.preimage A.continuous)
  have hsec : ∀ x ∈ Y ∩ B, A x ≠ A w →
      ∃ (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
        DifferentiableOn ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ (Y ∩ B) ∩ V = g '' O := by
    intro x hx hne
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ :=
      hsheet x ⟨hx.1, ball_subset_closedBall hx.2.1⟩ hne hx.2.2
    have hgc : ContinuousOn g O := hg.continuousOn
    refine ⟨O ∩ g ⁻¹' B, V ∩ B, g, hgc.isOpen_inter_preimage hO hBopen, hV.inter hBopen, ⟨hxV, hx.2⟩,
      hg.differentiableOn.mono Set.inter_subset_left, fun t ht => hAg t ht.1, ?_⟩
    rw [Set.image_inter_preimage, ← hYV]
    ext z
    simp only [Set.mem_inter_iff]
    tauto
  obtain ⟨N, hN⟩ := hCount σ (Y ∩ B) 1 A (ball (A w) ρ) (fun y => y 0 - A w 0) isOpen_ball
    (convex_ball (A w) ρ).isPreconnected (fun x hx => hx.2.2)
    (fun K hK hKc => hclosed K hKc.isClosed hK)
    (fun y _ => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt y).sub
      analyticAt_const)
    (fun x hx hne => by
      obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx (fun h => hne (by simp [h]))
      exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hYV⟩)
  refine ⟨N, ?_⟩
  unfold IsCentredDiscCover
  refine ⟨⟨hw, mem_ball_self hr, mem_ball_self hρ⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnh := Filter.inter_mem hsurj (ball_mem_nhds (A w) hρ)
    have hnb : (𝓝[≠] (A w)).NeBot := Module.punctured_nhds_neBot ℂ (Fin 1 → ℂ) (A w)
    obtain ⟨y, ⟨⟨x, hx, hxy⟩, hyD⟩, hyne⟩ :=
      Filter.nonempty_of_mem
        (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hnh) self_mem_nhdsWithin : _ ∈ 𝓝[≠] (A w))
    have hc := hN y hyD (sub_ne_zero.2 fun h => hyne (line_ext h))
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      subst h0
      have hempty : {z | z ∈ Y ∩ B ∧ A z = y} = ∅ := Set.encard_eq_zero.1 (by simpa using hc)
      have hmem : x ∈ {z | z ∈ Y ∩ B ∧ A z = y} :=
        ⟨⟨hx.1, hx.2, by simpa [Set.mem_preimage, hxy] using hyD⟩, hxy⟩
      rw [hempty] at hmem
      exact hmem
    · exact h0
  · exact fun x hx => mem_line_ball.1 hx.2.2
  · exact fun x hx hpx => hiso x ⟨hx.1, ball_subset_closedBall hx.2.1⟩ (line_ext hpx)
  · intro t ht hne
    have hc : (fun _ : Fin 1 => t) ∈ ball (A w) ρ := mem_line_ball.2 ht
    have h := hN (fun _ => t) hc (sub_ne_zero.2 hne)
    have heq : {x | x ∈ Y ∩ B ∧
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp A) x = t} =
        {x | x ∈ Y ∩ B ∧ A x = fun _ => t} := by
      ext x
      constructor
      · rintro ⟨hx, h1⟩
        exact ⟨hx, line_ext h1⟩
      · rintro ⟨hx, h1⟩
        refine ⟨hx, ?_⟩
        show A x 0 = t
        rw [h1]
    rw [heq]
    exact h
  · intro K hK hKc
    exact hclosed ((fun y : Fin 1 → ℂ => y 0) ⁻¹' K) (hKc.isClosed.preimage (continuous_apply 0))
      (fun y hy => mem_line_ball.2 (hK hy))
  · intro x hx hne
    have hne' : A x ≠ A w := fun h => hne (by
      show A x 0 = A w 0
      rw [h])
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx hne'
    have hcc : Continuous (fun (t : ℂ) (_ : Fin 1) => t) := continuous_pi fun _ => continuous_id
    have hcd : Differentiable ℂ (fun (t : ℂ) (_ : Fin 1) => t) :=
      differentiable_pi.2 fun _ => differentiable_id
    have hcs : Function.Surjective (fun (t : ℂ) (_ : Fin 1) => t) := fun y => ⟨y 0, const_coord y⟩
    refine ⟨(fun (t : ℂ) (_ : Fin 1) => t) ⁻¹' O, V, g ∘ (fun (t : ℂ) (_ : Fin 1) => t),
      hO.preimage hcc, hV, hxV, hg.comp hcd.differentiableOn (fun t ht => ht), fun t ht => ?_, ?_⟩
    · show A (g (fun _ => t)) 0 = t
      rw [hAg _ ht]
    · rw [Set.image_comp, Set.image_preimage_eq O hcs]
      exact hYV

end GlobalTheory.CompanionTheory.ComplexSets.DiscCover

namespace GlobalTheory.CompanionTheory.ComplexSets

open Metric DiscCover

theorem irreducibleGerm_contains_centredDiscCover :
    FiniteGermProjectionOpenAt.Statement → IrreducibleGermPrimitiveForm.Statement →
    PrimitiveFormSheetedOffDiscriminant.Statement → UnbranchedProperCountConstant.Statement →
    ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)),
      IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) →
      (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
      ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N := by
  intro hOpen hPrim hSheet hCount σ _ Y w A hAn hIrr hIso hDom
  obtain ⟨ℓ, N0, a, δ, q, ha, hδ, hq, hδne, hp1, hsep, hcoord⟩ := hPrim σ Y w 1 A hAn hIrr hIso hDom
  obtain ⟨M, hM, hMs⟩ := hSheet σ Y w 1 A hAn hIrr hIso hDom ℓ N0 a δ q ha hδ hq hδne hp1 hsep hcoord
  obtain ⟨ρ₀, hρ₀, hδ0⟩ := exists_punctured_ball_ne_zero δ (A w) hδ hδne
  have hAn2 := hAn
  have hIso2 := hIso
  obtain ⟨Nn, k, f, hNo, hwN, hf, hYN⟩ := hAn2
  obtain ⟨W', hW', hiso⟩ := hIso2
  have hU : M ∩ Nn ∩ W' ∈ 𝓝 w := Filter.inter_mem (Filter.inter_mem hM (hNo.mem_nhds hwN)) hW'
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU
  have hcomp : IsCompact (Y ∩ closedBall w r) :=
    isCompact_inter_of_cut hf hYN (isCompact_closedBall w r) (fun x hx => (hrU hx).1.2)
  have hS : IsCompact ((Y ∩ closedBall w r) ∩ sphere w r) := hcomp.inter_right isClosed_sphere
  have hAS : A w ∉ A '' ((Y ∩ closedBall w r) ∩ sphere w r) := by
    rintro ⟨x, ⟨⟨hxY, hxb⟩, hxs⟩, hx⟩
    have hxw := hiso x ⟨hxY, (hrU hxb).2⟩ hx
    rw [hxw, mem_sphere, dist_self] at hxs
    exact hr.ne hxs
  have hnh : (A '' ((Y ∩ closedBall w r) ∩ sphere w r))ᶜ ∈ 𝓝 (A w) :=
    (hS.image A.continuous).isClosed.isOpen_compl.mem_nhds hAS
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.mem_nhds_iff.1 hnh
  obtain ⟨N, hN⟩ := cover_of_radii hCount σ Y w A r (min ρ₀ ρ₁) hr (lt_min hρ₀ hρ₁) hIrr.1 hcomp
    (fun x hxY hd hb => hball (ball_subset_ball (min_le_right _ _) hb)
      ⟨x, ⟨⟨hxY, mem_closedBall.2 hd.le⟩, mem_sphere.2 hd⟩, rfl⟩)
    (fun x hx hxe => hiso x ⟨hx.1, (hrU hx.2).2⟩ hxe)
    (fun x hx hne hb => hMs x ⟨hx.1, (hrU hx.2).1.1⟩
      (hδ0 (A x) (ball_subset_ball (min_le_left _ _) hb) hne))
    (hOpen σ Y w 1 A hAn hIso hDom (ball w r) (ball_mem_nhds w hr))
  exact ⟨_, _, _, N, fun x hx => hx.1, hN⟩

end GlobalTheory.CompanionTheory.ComplexSets
