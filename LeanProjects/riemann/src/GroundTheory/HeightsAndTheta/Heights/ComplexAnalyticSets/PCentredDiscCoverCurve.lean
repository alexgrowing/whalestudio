import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCentredDiscCoverCurve
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCoverCycles
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Matrix

noncomputable section

theorem centredDiscCover_punctured_branch (hPCC : PuncturedCoverCycles.Statement)
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) :
    ∃ (δ : ℝ) (k : ℕ) (φ : ℂ → σ → ℂ), 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ k ∧
      DifferentiableOn ℂ φ (ball 0 δ \ {0}) ∧ Set.InjOn φ (ball 0 δ \ {0}) ∧
      ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k := by
  obtain ⟨hwY, hN, hmaps, huniq, hcard, -, hsec⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let Φ : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv
  let L : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    ContinuousLinearMap.pi fun _ => p.comp (Φ : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))
  let A : Matrix (Fin (0 + 1)) (Fin (Fintype.card σ)) ℂ :=
    LinearMap.toMatrix' (L : (Fin (Fintype.card σ) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
  have hA : ∀ z, A *ᵥ z = fun _ => p (Φ z) := fun z => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hpT : ∀ z, p (w + Φ z) = p w + p (Φ z) := fun z => map_add p w (Φ z)
  have hT : ∀ x, w + Φ (Φ.symm (x - w)) = x := fun x => by simp
  have hone : ∀ (y : Fin (0 + 1) → ℂ) (t : ℂ), t = y 0 → (fun _ => t) = y := fun y t ht => by
    funext i
    rw [show i = 0 from Subsingleton.elim (α := Fin 1) _ _, ht]
  let X : Set (Fin (Fintype.card σ) → ℂ) := {z | w + Φ z ∈ Y ∧ p (Φ z) ≠ 0}
  obtain ⟨m, ord, ψ, δ, hδ, hδ1, hsum, hord, hdiff, hmap, hinj, -, -⟩ :=
    hPCC (Fintype.card σ) 0 N A 0 ρ X hρ rfl
      (fun x hx => by
        rw [hA, dist_zero_right, pi_norm_const]
        refine ⟨?_, hx.2⟩
        have := hmaps hx.1
        rwa [mem_ball, dist_eq_norm, hpT, add_sub_cancel_left] at this)
      (fun y hy hy0 => by
        have hyρ : p w + y 0 ∈ ball (p w) ρ := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
          exact (norm_le_pi_norm y 0).trans_lt (by rwa [dist_zero_right] at hy)
        rw [← hcard _ hyρ (by simpa using hy0), ← ((add_right_injective w).comp Φ.injective).injOn.encard_image]
        congr 1
        ext x
        constructor
        · rintro ⟨z, ⟨⟨hzY, -⟩, hzy⟩, rfl⟩
          refine ⟨hzY, ?_⟩
          rw [Function.comp_apply, hpT, ← congrFun ((hA z).symm.trans hzy) 0]
        · rintro ⟨hxY, hxp⟩
          refine ⟨Φ.symm (x - w), ⟨⟨by rwa [hT], ?_⟩, ?_⟩, hT x⟩
          · simpa [hxp] using hy0
          · rw [hA]
            exact hone y _ (by simp [hxp]))
      (fun x hx => by
        obtain ⟨O₀, V₀, g₀, hO₀, hV₀, hxV₀, hg₀, hpg₀, hYV⟩ :=
          hsec (w + Φ x) hx.1 (by rw [hpT]; simpa using hx.2)
        have hsec' : ∀ z, w + Φ z ∈ Y ∩ V₀ → p w + p (Φ z) ∈ O₀ ∧ g₀ (p w + p (Φ z)) = w + Φ z := by
          intro z hz
          rw [hYV] at hz
          obtain ⟨t, ht, hgt⟩ := hz
          have : t = p w + p (Φ z) := by rw [← hpT, ← hgt, hpg₀ t ht]
          subst this
          exact ⟨ht, hgt⟩
        obtain ⟨hxO, hgx⟩ := hsec' x ⟨hx.1, hxV₀⟩
        refine ⟨{y | p w + y 0 ∈ O₀ ∧ y 0 ≠ 0}, {z | w + Φ z ∈ V₀ ∧ p (Φ z) ≠ 0},
          fun y => Φ.symm (g₀ (p w + y 0) - w),
          (hO₀.preimage (continuous_const.add (continuous_apply 0))).inter
            (isOpen_ne_fun (continuous_apply 0) continuous_const),
          by rw [hA]; exact ⟨hxO, hx.2⟩,
          (hV₀.preimage (continuous_const.add Φ.continuous)).inter
            (isOpen_ne_fun (p.continuous.comp Φ.continuous) continuous_const),
          ⟨hxV₀, hx.2⟩, ?_, by rw [hA]; simp [hgx], fun y hy => ?_, ?_⟩
        · exact Φ.symm.differentiable.comp_differentiableOn
            ((hg₀.comp ((differentiableOn_const _).add (differentiable_apply 0).differentiableOn)
              fun y hy => hy.1).sub_const w)
        · rw [hA]
          refine hone y _ ?_
          simp [hpg₀ _ hy.1]
        · ext z
          constructor
          · rintro ⟨⟨hzY, hz0⟩, hzV, -⟩
            obtain ⟨hzO, hgz⟩ := hsec' z ⟨hzY, hzV⟩
            exact ⟨fun _ => p (Φ z), ⟨hzO, hz0⟩, by simp [hgz]⟩
          · rintro ⟨y, ⟨hyO, hy0⟩, rfl⟩
            have hw : w + Φ (Φ.symm (g₀ (p w + y 0) - w)) = g₀ (p w + y 0) := hT _
            have hp : p (Φ (Φ.symm (g₀ (p w + y 0) - w))) = y 0 := by simp [hpg₀ _ hyO]
            have hmem : g₀ (p w + y 0) ∈ Y ∩ V₀ := by rw [hYV]; exact ⟨_, hyO, rfl⟩
            show (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ Y ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0) ∧
              (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ V₀ ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0)
            rw [hw, hp]
            exact ⟨⟨hmem.1, hy0⟩, hmem.2, hy0⟩)
  obtain ⟨b⟩ : Nonempty (Fin m) := by
    rcases m with _ | m
    · simp at hsum
      omega
    · exact ⟨0⟩
  have hpunct : ∀ s ∈ ball (0 : ℂ) δ \ {0},
      (fun _ => s) ∈ ball (0 : Fin (0 + 1) → ℂ) δ ∩ {t | t 0 ≠ 0} := fun s hs =>
    ⟨by rw [mem_ball, dist_zero_right, pi_norm_const]; exact mem_ball_zero_iff.1 hs.1, hs.2⟩
  refine ⟨δ, ord b, fun s => w + Φ (ψ b fun _ => s), hδ, hδ1, hord b, ?_, ?_, fun s hs => ?_⟩
  · exact (differentiableOn_const w).add (Φ.differentiable.comp_differentiableOn
      ((hdiff b).comp (differentiable_pi.2 fun _ => differentiable_id).differentiableOn hpunct))
  · intro s hs s' hs' hss'
    have := hinj b (hpunct s hs) (hpunct s' hs') (Φ.injective (add_left_cancel hss'))
    exact congrFun this 0
  · obtain ⟨hX, hAψ⟩ := hmap b _ (hpunct s hs)
    refine ⟨hX.1, ?_⟩
    rw [hpT]
    have := congrFun ((hA _).symm.trans hAψ) 0
    simp only [Function.update_self] at this
    rw [this]

theorem centredDiscCover_extend_across_centre
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) {δ : ℝ} {k : ℕ} {φ : ℂ → σ → ℂ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 1 ≤ k) (hφd : DifferentiableOn ℂ φ (ball 0 δ \ {0})) (hφi : Set.InjOn φ (ball 0 δ \ {0}))
    (hφY : ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k) :
    ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
      DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y := by
  obtain ⟨hwY, -, hmaps, huniq, -, hprop, -⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  set r := min δ (ρ / 2) with hr
  have hr0 : 0 < r := lt_min hδ (half_pos hρ)
  have hrδ : ball (0 : ℂ) r \ {0} ⊆ ball 0 δ \ {0} :=
    Set.sdiff_subset_sdiff_left (ball_subset_ball (min_le_left _ _))
  have hK : IsCompact {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hprop _ (closedBall_subset_ball (half_lt_self hρ)) (isCompact_closedBall _ _)
  have hφK : ∀ s ∈ ball (0 : ℂ) r \ {0}, φ s ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} := by
    intro s hs
    obtain ⟨hY', hp⟩ := hφY s (hrδ hs)
    refine ⟨hY', ?_⟩
    rw [mem_closedBall, hp, dist_eq_norm, add_sub_cancel_left, norm_pow]
    have h1 : ‖s‖ < r := mem_ball_zero_iff.1 hs.1
    calc ‖s‖ ^ k ≤ ‖s‖ :=
          pow_le_of_le_one (norm_nonneg _) (h1.le.trans ((min_le_left _ _).trans hδ1)) (by omega)
      _ ≤ ρ / 2 := h1.le.trans (min_le_right _ _)
  have hbdd : BddAbove (norm ∘ φ '' (ball 0 r \ {0})) := by
    refine (hK.image continuous_norm).bddAbove.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨φ s, hφK s hs, rfl⟩
  have hF := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr0) (hφd.mono hrδ) hbdd
  set ℓ := limUnder (𝓝[≠] (0 : ℂ)) φ with hℓdef
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ∈ ball (0 : ℂ) r \ {0} := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds 0 hr0)] with s h1 h2
    exact ⟨h2, h1⟩
  have hlim : Tendsto φ (𝓝[≠] 0) (𝓝 ℓ) := by
    have hc := (hF.continuousOn.continuousAt (ball_mem_nhds 0 hr0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [Function.update_self] at hc
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Function.update_of_ne hs _ _
  have hℓK : ℓ ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hK.isClosed.mem_of_tendsto hlim (hev.mono hφK)
  have hpℓ : p ℓ = p w := by
    have h1 : Tendsto (fun s => p (φ s)) (𝓝[≠] 0) (𝓝 (p ℓ)) := (p.continuous.tendsto ℓ).comp hlim
    have h2 : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝[≠] 0) (𝓝 (p w)) := by
      have : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝 0) (𝓝 (p w + 0 ^ k)) :=
        (continuous_const.add (continuous_pow k)).tendsto 0
      rw [zero_pow (by omega), add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [hev] with s hs
    exact (hφY s (hrδ hs)).2
  have hℓ : ℓ = w := huniq ℓ hℓK.1 hpℓ
  refine ⟨r, hr0, Function.update φ 0 w, ?_, ?_, Function.update_self _ _ _, ?_⟩
  · rw [← hℓ]
    exact hF
  · have hoff : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → Function.update φ 0 w s ≠ w := by
      intro s hs h0 heq
      rw [Function.update_of_ne h0] at heq
      have := (hφY s (hrδ ⟨hs, h0⟩)).2
      rw [heq] at this
      exact pow_ne_zero k h0 (by linear_combination -this)
    intro s hs s' hs' hss'
    by_cases h0 : s = 0 <;> by_cases h0' : s' = 0
    · rw [h0, h0']
    · subst h0
      rw [Function.update_self] at hss'
      exact absurd hss'.symm (hoff s' hs' h0')
    · subst h0'
      rw [Function.update_self] at hss'
      exact absurd hss' (hoff s hs h0)
    · rw [Function.update_of_ne h0, Function.update_of_ne h0'] at hss'
      exact hφi (hrδ ⟨hs, h0⟩) (hrδ ⟨hs', h0'⟩) hss'
  · intro s hs
    by_cases h0 : s = 0
    · subst h0
      rw [Function.update_self]
      exact hwY
    · rw [Function.update_of_ne h0]
      exact (hφY s (hrδ ⟨hs, h0⟩)).1

theorem CentredDiscCoverCurve.proof (hPCC : PuncturedCoverCycles.Statement) :
    CentredDiscCoverCurve.Statement := by
  intro σ _ Y w p ρ N hY
  obtain ⟨δ, k, φ, hδ, hδ1, hk, hφd, hφi, hφY⟩ := centredDiscCover_punctured_branch hPCC hY
  exact centredDiscCover_extend_across_centre hY hδ hδ1 hk hφd hφi hφY

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
