import Mathlib
open Filter Topology

private theorem UpperTheory.exists_character_nontrivial_off {G : Type} [CommGroup G] (H : Subgroup G) {a : G} (ha : a ∉ H) :
    ∃ ψ : G →* Circle, (∀ u ∈ H, ψ u = 1) ∧ ψ a ≠ 1 := by
  have hne : (Additive.ofMul (a : G ⧸ H)) ≠ 0 := fun h => ha ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let e : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro _ ⟨k, rfl⟩
      exact ⟨k, by simp⟩)
  have he : ∀ a, e a = 0 → a = 0 := by
    intro a
    induction a using QuotientAddGroup.induction_on with
    | H q =>
      intro h
      have h1 : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
      rw [AddCircle.coe_eq_zero_iff] at h1 ⊢
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      have : ((k : ℚ) : ℝ) = q := by simpa using hk
      have h5 : (k : ℚ) = q := by exact_mod_cast this
      simpa using h5
  let f : G → AddCircle (1 : ℝ) := fun x => e (χ (Additive.ofMul (x : G ⧸ H)))
  have hf1 : f 1 = 0 := by
    show e (χ 0) = 0
    rw [map_zero, map_zero]
  have hfm : ∀ a b, f (a * b) = f a + f b := by
    intro a b
    show e (χ (Additive.ofMul (a : G ⧸ H) + Additive.ofMul (b : G ⧸ H))) = _
    rw [map_add, map_add]
  let ψ : G →* Circle :=
    { toFun := fun x => AddCircle.toCircle (f x)
      map_one' := by rw [hf1, AddCircle.toCircle_zero]
      map_mul' := fun a b => by rw [hfm, AddCircle.toCircle_add] }
  refine ⟨ψ, fun u hu => ?_, ?_⟩
  · have h0 : (u : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).2 hu
    have : f u = 0 := by
      show e (χ (Additive.ofMul (u : G ⧸ H))) = 0
      rw [h0, ofMul_one, map_zero, map_zero]
    show AddCircle.toCircle (f u) = 1
    rw [this, AddCircle.toCircle_zero]
  · intro h
    have h2 : AddCircle.toCircle (f a) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h
    exact hχ (he _ (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero h2))

theorem UpperTheory.closed_subgroup_eq_top_of_dense :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Subgroup G), IsClosed (M : Set G) →
        (∀ μ : G →* Circle, Continuous μ → (∀ m ∈ M, μ m = 1) → μ = 1) →
        (∀ W ∈ nhds (1 : G), ∃ O : OpenSubgroup G, ∀ o ∈ O, ∃ m ∈ M, ∃ w ∈ W, o = m * w) → M = ⊤ := by
  intro G _ _ _ M hM hchar hsmall
  have step1 : ∀ (O : OpenSubgroup G) (g : G), g ∈ M ⊔ O.toSubgroup := by
    intro O g
    by_contra hg
    obtain ⟨ψ, h1, h2⟩ := UpperTheory.exists_character_nontrivial_off _ hg
    have hc : Continuous ψ := by
      apply continuous_of_continuousAt_one
      have hev : (fun _ : G => (1 : Circle)) =ᶠ[nhds (1 : G)] ψ := by
        filter_upwards [O.mem_nhds_one] with x hx
        exact (h1 x (Subgroup.mem_sup_right hx)).symm
      exact continuousAt_const.congr hev
    have := hchar ψ hc (fun m hm => h1 m (Subgroup.mem_sup_left hm))
    exact h2 (by rw [this]; rfl)
  rw [eq_top_iff]
  intro g _
  have : g ∈ closure (M : Set G) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hcont : Continuous (fun w : G => g * w⁻¹) := by fun_prop
    have hW : (fun w : G => g * w⁻¹) ⁻¹' U ∈ nhds (1 : G) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨O, hO⟩ := hsmall _ hW
    obtain ⟨m, hm, o, ho, hmo⟩ := Subgroup.mem_sup.1 (step1 O g)
    obtain ⟨m', hm', w, hw, rfl⟩ := hO o ho
    refine ⟨g * w⁻¹, hw, ?_⟩
    have : g * w⁻¹ = m * m' := by rw [← hmo]; group
    rw [this]
    exact M.mul_mem hm hm'
  rwa [hM.closure_eq] at this
