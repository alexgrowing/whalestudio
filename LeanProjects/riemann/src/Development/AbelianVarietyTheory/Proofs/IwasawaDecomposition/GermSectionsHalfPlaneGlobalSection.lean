import Mathlib
open Filter Topology

namespace GlobalTheory

theorem germSections_glue {Y ι : Type} (G : ℂ → (ℂ → Y) → Prop)
    (h1 : ∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s') (i₀ : ι)
    (U : ι → Set ℂ) (s : ι → ℂ → Y) (hU : ∀ i, IsOpen (U i))
    (hs : ∀ i, ∀ z ∈ U i, G z (s i))
    (hag : ∀ i j, Set.EqOn (s i) (s j) (U i ∩ U j)) :
    ∃ t : ℂ → Y, ∀ i, ∀ z ∈ U i, G z t := by
  classical
  refine ⟨fun z => if h : ∃ i, z ∈ U i then s h.choose z else s i₀ z, fun i z hz => ?_⟩
  refine h1 z (s i) _ ?_ (hs i z hz)
  filter_upwards [(hU i).mem_nhds hz] with w hw
  have h : ∃ i, w ∈ U i := ⟨i, hw⟩
  rw [dif_pos h]
  exact hag i _ ⟨hw, h.choose_spec⟩

theorem germSections_halfPlane_global (Y : Type) (G : ℂ → (ℂ → Y) → Prop) (T : ℝ)
    (h1 : ∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s')
    (h2 : ∀ w : ℂ, T < w.im → ∃ s, ∀ᶠ z in 𝓝 w, G z s)
    (h3 : ∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) →
      (∀ z ∈ U, G z s) → (∀ z ∈ U, G z s') → ∀ w ∈ U, s w = s' w → Set.EqOn s s' U)
    (h4 : ∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) →
      (∀ z ∈ U, G z s) → ∀ w ∈ U, G w s' → ∃ s'' : ℂ → Y, (∀ z ∈ U, G z s'') ∧ s'' w = s' w) :
    ∃ s : ℂ → Y, ∀ w : ℂ, T < w.im → G w s := by
  have hH : IsOpen {z : ℂ | T < z.im} := isOpen_lt continuous_const Complex.continuous_im

  have glue : ∀ {ι : Type} (_ : ι) (U : ι → Set ℂ) (p : ℂ), (∀ i, IsOpen (U i)) →
      (∀ i, Convex ℝ (U i)) → (∀ i, ∀ z ∈ U i, T < z.im) → (∀ i, p ∈ U i) →
      (∀ i, ∃ s, ∀ z ∈ U i, G z s) → ∃ t : ℂ → Y, ∀ i, ∀ z ∈ U i, G z t := by
    intro ι i₀ U p ho hc hT hp hs
    obtain ⟨s₀, hs₀⟩ := hs i₀
    have : ∀ i, ∃ s : ℂ → Y, (∀ z ∈ U i, G z s) ∧ s p = s₀ p := fun i => by
      obtain ⟨s, hs⟩ := hs i
      exact h4 (U i) s s₀ (ho i) (hc i) (hT i) hs p (hp i) (hs₀ p (hp i₀))
    choose s hs hsp using this
    refine germSections_glue G h1 i₀ U s ho hs fun i j => ?_
    exact h3 (U i ∩ U j) (s i) (s j) ((ho i).inter (ho j)) ((hc i).inter (hc j))
      (fun z hz => hT i z hz.1) (fun z hz => hs i z hz.1) (fun z hz => hs j z hz.2) p
      ⟨hp i, hp j⟩ ((hsp i).trans (hsp j).symm)
  have loc : ∀ w : ℂ, T < w.im → ∃ D : Set ℂ, IsOpen D ∧ Convex ℝ D ∧ (∀ z ∈ D, T < z.im) ∧
      w ∈ D ∧ ∃ s, ∀ z ∈ D, G z s := by
    intro w hw
    obtain ⟨s, hs⟩ := h2 w hw
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hs.and (hH.mem_nhds hw))
    exact ⟨Metric.ball w ε, Metric.isOpen_ball, convex_ball w ε, fun z hz => (hb z hz).2,
      Metric.mem_ball_self hε, s, fun z hz => (hb z hz).1⟩
  set p : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hpdef
  have hp : T < p.im := by simp [hpdef]
  let good : ℂ → Prop := fun w => ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ (∀ z ∈ U, T < z.im) ∧
      p ∈ U ∧ w ∈ U ∧ ∃ s, ∀ z ∈ U, G z s
  have hgood : ∀ w : ℂ, T < w.im → good w := by
    intro w hw
    let γ : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap p w
    have hγc : Continuous γ := AffineMap.lineMap_continuous
    have hγ0 : γ 0 = p := AffineMap.lineMap_apply_zero p w
    have hγ1 : γ 1 = w := AffineMap.lineMap_apply_one p w
    have hγH : ∀ t ∈ Set.Icc (0 : ℝ) 1, T < (γ t).im := by
      intro t ht
      have hc := ((convex_halfSpace_im_gt T).affine_preimage γ).ordConnected
      exact hc.out (x := 0) (y := 1) (by simpa [hγ0] using hp) (by simpa [hγ1] using hw) ht
    have step : ∀ D : Set ℂ, IsOpen D → Convex ℝ D → (∀ z ∈ D, T < z.im) →
        (∃ s, ∀ z ∈ D, G z s) → ∀ a b : ℝ, 0 ≤ b → γ a ∈ D → γ b ∈ D →
        good (γ a) → good (γ b) := by
      rintro D hDo hDc hDT hDs a b hb ha hbD ⟨U, hUo, hUc, hUT, hpU, haU, hUs⟩
      obtain ⟨t, ht⟩ := glue true (fun i : Bool => cond i U D) (γ a)
        (by rintro (_ | _) <;> assumption) (by rintro (_ | _) <;> assumption)
        (by rintro (_ | _) <;> assumption) (by rintro (_ | _) <;> assumption)
        (by rintro (_ | _) <;> assumption)
      have hK : IsCompact (γ '' Set.Icc 0 b) := isCompact_Icc.image hγc
      have hKc : Convex ℝ (γ '' Set.Icc 0 b) := (convex_Icc 0 b).affine_image γ
      have hsub : γ '' Set.Icc 0 b ⊆ U ∪ D := by
        rintro _ ⟨r, hr, rfl⟩
        rcases le_total r a with h | h
        · left
          exact (hUc.affine_preimage γ).ordConnected.out (x := 0) (y := a)
            (by simpa [hγ0] using hpU) haU ⟨hr.1, h⟩
        · right
          exact (hDc.affine_preimage γ).ordConnected.out (x := a) (y := b) ha hbD ⟨h, hr.2⟩
      obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open (hUo.union hDo) hsub
      refine ⟨Metric.thickening δ (γ '' Set.Icc 0 b), Metric.isOpen_thickening,
        hKc.thickening δ, fun z hz => ?_, ?_, ?_, t, fun z hz => ?_⟩
      · rcases hth hz with h | h
        · exact hUT z h
        · exact hDT z h
      · exact Metric.self_subset_thickening hδ _ ⟨0, ⟨le_rfl, hb⟩, hγ0⟩
      · exact Metric.self_subset_thickening hδ _ ⟨b, ⟨hb, le_rfl⟩, rfl⟩
      · rcases hth hz with h | h
        · exact ht true z h
        · exact ht false z h
    have key := (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).induction₂'
      (fun a b => good (γ a) → good (γ b)) (by
        intro x hx
        obtain ⟨D, hDo, hDc, hDT, hxD, hDs⟩ := loc (γ x) (hγH x hx)
        have : ∀ᶠ y in 𝓝 x, γ y ∈ D := hγc.continuousAt.eventually (hDo.mem_nhds hxD)
        filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with y hy hyI
        exact ⟨step D hDo hDc hDT hDs x y hyI.1 hxD hy, step D hDo hDc hDT hDs y x hx.1 hy hxD⟩)
      (fun _ _ _ _ _ _ h h' hh => h' (h hh)) (x := 0) (y := 1) (by simp) (by simp)
    rw [hγ0, hγ1] at key
    apply key
    obtain ⟨D, hDo, hDc, hDT, hxD, hDs⟩ := loc p hp
    exact ⟨D, hDo, hDc, hDT, hxD, hxD, hDs⟩
  choose U hUo hUc hUT hpU hwU hUs using hgood
  obtain ⟨t, ht⟩ := glue (ι := {w : ℂ // T < w.im}) ⟨p, hp⟩ (fun w => U w.1 w.2) p
    (fun w => hUo w.1 w.2) (fun w => hUc w.1 w.2) (fun w => hUT w.1 w.2) (fun w => hpU w.1 w.2)
    (fun w => hUs w.1 w.2)
  exact ⟨t, fun w hw => ht ⟨w, hw⟩ w (hwU w hw)⟩

end GlobalTheory
