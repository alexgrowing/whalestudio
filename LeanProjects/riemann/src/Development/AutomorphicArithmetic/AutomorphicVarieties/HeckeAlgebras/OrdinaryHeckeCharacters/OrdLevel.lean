import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.ordLevel :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ U V : Subgroup X.Ub, V ≤ U → V.relIndex U ≠ 0 → X.FinLevel U → X.Free τ θ U → X.FinLevel V ∧ X.Free τ θ V ∧ X.Ord τ θ U = X.Ord τ θ V ⊓ fixd (X.ra τ) U := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ U V hVU hidx hU hF
  refine ⟨?_, ?_, ?_⟩
  · classical
    unfold Frame.FinLevel at hU ⊢
    obtain ⟨s, hs⟩ := hU
    haveI : (V.subgroupOf U).FiniteIndex := ⟨hidx⟩
    haveI : Fintype (U ⧸ V.subgroupOf U) := Fintype.ofFinite _
    refine ⟨(s ×ˢ (Finset.univ : Finset (U ⧸ V.subgroupOf U))).image
      (fun p => p.1 * ((((Quotient.out p.2 : U) : X.Ub) : Ga), (1 : Gp))), ?_⟩
    intro g
    obtain ⟨γ, x, hx, u, hu, b, hb, rfl⟩ := hs g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf U) (⟨u, hu⟩ : U)
    have hmem : (x, (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ V.subgroupOf U)) ∈
        s ×ˢ (Finset.univ : Finset (U ⧸ V.subgroupOf U)) :=
      Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩
    refine ⟨γ, _, Finset.mem_image_of_mem _ hmem,
      ((h⁻¹ : V.subgroupOf U) : U), Subgroup.mem_subgroupOf.mp (h⁻¹).2, b, hb, ?_⟩
    simp only at hh ⊢
    rw [hh]
    simp [Prod.ext_iff, mul_assoc]
  · unfold Frame.Free at hF ⊢
    intro g γ u hu b hb h
    exact hF g γ u (hVU hu) b hb h
  · have hfix : fixd (X.ra τ) U ≤ fixd (X.ra τ) V := by
      unfold fixd
      intro f hf u hu
      exact hf u (hVU hu)
    unfold Frame.Ord Frame.Sp
    apply le_antisymm
    · intro f hf
      simp only [Submodule.mem_inf] at hf ⊢
      exact ⟨⟨⟨hf.1.1, hfix hf.1.2⟩, hf.2⟩, hf.1.2⟩
    · intro f hf
      simp only [Submodule.mem_inf] at hf ⊢
      exact ⟨⟨hf.1.1.1, hf.2⟩, hf.1.2⟩
