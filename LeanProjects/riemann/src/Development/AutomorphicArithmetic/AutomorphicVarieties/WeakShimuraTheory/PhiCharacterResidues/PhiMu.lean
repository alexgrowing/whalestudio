import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiMu :
    ∀ {l : ℕ} [Fact l.Prime] {H Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (f : H →* Γ), Continuous f → ∀ D : Subgroup Γ, (∀ g, f g ∈ D) → ∀ g ∈ W.muG l H, f g ∈ muOf l D := by
  intro l _ H Γ _ _ _ _ _ _ f hf D hD g hg
  refine ⟨hD g, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (QuotientGroup.mk' (commutator H).topologicalClosure g) ^ l ^ k = 1 := hg
  refine ⟨k, ?_⟩
  have h1 : g ^ l ^ k ∈ (commutator H).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact hk
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
  rw [← map_pow, ← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  have hle : (⊤ : Subgroup H).map f ≤ D := by
    rintro _ ⟨x, _, rfl⟩
    exact hD x
  have h3 : f '' (commutator H : Set H) ⊆ ((⁅D, D⁆ : Subgroup Γ) : Set Γ) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : f x ∈ (commutator H).map f := ⟨x, hx, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at hx'
    exact Subgroup.commutator_mono hle hle hx'
  exact closure_mono h3 (image_closure_subset_closure_image hf ⟨_, h1, rfl⟩)
