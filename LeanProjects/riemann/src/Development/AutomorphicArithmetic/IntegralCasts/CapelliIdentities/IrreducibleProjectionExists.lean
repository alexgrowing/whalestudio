import Mathlib

private lemma sepCore {R S N ι : Type} [Ring R] [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    [AddCommGroup N] [Module R N] (f : ι → S →ₗ[R] N)
    (h : ⨆ i, LinearMap.range (f i) = ⊤) {x : N} (hx : x ≠ 0) :
    ∃ p : N →ₗ[R] S, p x ≠ 0 := by
  have hss : ∀ i, IsSemisimpleModule R (LinearMap.range (f i)) := fun i => .range (f i)
  have : IsSemisimpleModule R N := isSemisimpleModule_of_isSemisimpleModule_submodule' hss h
  have hiso : IsIsotypicOfType R N S := by
    apply IsIsotypicOfType.of_isotypicComponent_eq_top
    rw [eq_top_iff, ← h]
    refine iSup_le fun i => ?_
    rcases (f i).injective_or_eq_zero with hi | hi
    · exact le_sSup ⟨(LinearEquiv.ofInjective (f i) hi).symm⟩
    · rw [hi, LinearMap.range_zero]
      exact bot_le
  obtain ⟨κ, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  have hne : e x ≠ 0 := (LinearEquiv.map_ne_zero_iff e).mpr hx
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  exact ⟨(Finsupp.lapply i) ∘ₗ e.toLinearMap, by simpa using hi⟩

theorem UpperTheory.irreducible_projection_exists :
    ∀ {H V M : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
        (σ : Representation ℂ H V) (ρ : Representation ℂ H M), σ.IsIrreducible →
        ∀ (Y : Submodule ℂ M),
          Y ≤ ⨆ (f : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y }),
            LinearMap.range f.1 →
          ∀ {F : M}, F ∈ Y → F ≠ 0 →
            ∃ p : M →ₗ[ℂ] V, (∀ (g : H), ∀ y ∈ Y, p (ρ g y) = σ g (p y)) ∧ p F ≠ 0 := by
  intro H V M _ _ _ _ _ σ ρ hσ Y hY F hF hF0
  have hinv : ∀ (g : H) {y : M}, y ∈ Y → ρ g y ∈ Y := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => ρ g y ∈ Y) (hY hy) ?_ ?_ ?_
    · rintro ⟨f, hf, hr⟩ x ⟨v, rfl⟩
      rw [← hf g v]
      exact hr ⟨_, rfl⟩
    · simp
    · intro a b ha hb
      rw [map_add]
      exact Y.add_mem ha hb
  let Ys : Subrepresentation ρ := ⟨Y, hinv⟩
  let τ : Representation ℂ H Y := Ys.toRepresentation
  let φ : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y } →
      Representation.IntertwiningMap σ τ := fun f =>
    (f.1.codRestrict Y (fun v => f.2.2 ⟨v, rfl⟩)).intertwiningMap_of_isIntertwiningMap σ τ
      (fun g v => Subtype.ext (f.2.1 g v))
  let ψ := fun i => Representation.IntertwiningMap.equivLinearMapAsModule σ τ (φ i)
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  have hall : ∀ y ∈ (⨆ (f : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y }),
      LinearMap.range f.1), ∃ hy : y ∈ Y,
      (show τ.asModule from (⟨y, hy⟩ : Y)) ∈ ⨆ i, LinearMap.range (ψ i) := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => ∃ hy : y ∈ Y,
      (show τ.asModule from (⟨y, hy⟩ : Y)) ∈ ⨆ i, LinearMap.range (ψ i)) hy ?_ ?_ ?_
    · rintro f x ⟨v, rfl⟩
      exact ⟨f.2.2 ⟨v, rfl⟩, Submodule.mem_iSup_of_mem f ⟨v, rfl⟩⟩
    · exact ⟨Y.zero_mem, Submodule.zero_mem _⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨Y.add_mem ha hb, Submodule.add_mem _ ha' hb'⟩
  have htop : ⨆ i, LinearMap.range (ψ i) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨_, hx⟩ := hall (x : Y).1 (hY (x : Y).2)
    exact hx
  obtain ⟨p, hp⟩ := sepCore ψ htop (x := (show τ.asModule from (⟨F, hF⟩ : Y)))
    (fun h => hF0 (congrArg Subtype.val (show (⟨F, hF⟩ : Y) = 0 from h)))
  let p' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm p
  obtain ⟨q, hq⟩ := LinearMap.exists_extend p'.toLinearMap
  have hqy : ∀ (y : M) (hy : y ∈ Y), q y = p' ⟨y, hy⟩ := fun y hy =>
    congrArg (fun l => l (⟨y, hy⟩ : Y)) hq
  refine ⟨q, fun g y hy => ?_, ?_⟩
  · rw [hqy _ (hinv g hy), hqy _ hy]
    exact Representation.IntertwiningMap.isIntertwining τ σ p' g ⟨y, hy⟩
  · rw [hqy _ hF]
    exact hp
