import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualZ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply

noncomputable section

section Helpers

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Count

variable {k G M : Type} [CommRing k] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k G M)

private def cls (L : Submodule k (H1 ρ)) : Set (G → M) :=
  {z | ∃ hz : z ∈ Z1 ρ, (Submodule.Quotient.mk ⟨z, hz⟩ : H1 ρ) ∈ L}

private theorem card_cls (h : ContAction ρ) (L : Submodule k (H1 ρ)) :
    (cls ρ L).ncard = Nat.card (B1 ρ) * Nat.card L := by
  have e1 : cls ρ L = Subtype.val '' ((fun z : Z1 ρ => (Submodule.Quotient.mk z : H1 ρ)) ⁻¹' (L : Set (H1 ρ))) := by
    ext z
    constructor
    · rintro ⟨hz, h⟩; exact ⟨⟨z, hz⟩, h, rfl⟩
    · rintro ⟨z, h, rfl⟩; exact ⟨z.2, h⟩
  have e2 := (Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet
    ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup (L : Set (H1 ρ)))).trans (Nat.card_prod _ _)
  have e3 : Nat.card ((B1 ρ).comap (Z1 ρ).subtype) = Nat.card (B1 ρ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles ρ h)).toEquiv
  rw [e1, Set.ncard_image_of_injective _ Subtype.val_injective, ← e3]
  exact e2

omit [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] in
private theorem card_coboundaries_mul_card_h0 : Nat.card (B1 ρ) * Nat.card (H0 ρ) = Nat.card M := by
  have e : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext m
    rw [LinearMap.mem_ker, funext_iff]
    exact forall_congr' fun g => sub_eq_zero
  rw [← e, Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 ρ)), mul_comm]
  congr 1
  exact (Nat.card_congr (d0 ρ).quotKerEquivRange.toEquiv).symm

private theorem Zl_iff (z : G → M) : z ∈ Zl ρ ↔ z ∈ Z1 ρ :=
  and_congr_left' (IsLocallyConstant.iff_continuous z)

private theorem fin_Zl [Finite M] [Finite (H1 ρ)] : Finite (Zl ρ) := by
  have : Finite (B1 ρ) := Finite.of_surjective _ (d0 ρ).surjective_rangeRestrict
  have : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  have : Finite (Z1 ρ) := Finite.of_equiv (H1 ρ × (B1 ρ).comap (Z1 ρ).subtype)
    (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup)).symm
  exact Finite.of_injective (fun x => (⟨x.1, (Zl_iff ρ _).1 x.2⟩ : Z1 ρ)) fun x y h => Subtype.ext (Subtype.mk.inj h)

end Count

private theorem ex_cls {n : ℕ} {G M : Type} [Group G] [TopologicalSpace G] [AddCommGroup M] [Module (ZMod n) M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod n) G M) (N : AddSubgroup (G → M))
    (h1 : (Bl ρ).toAddSubgroup ≤ N) (h2 : N ≤ (Zl ρ).toAddSubgroup) :
    ∃ L : Submodule (ZMod n) (H1 ρ), cls ρ L = N := by
  refine ⟨((AddSubgroup.toZModSubmodule n N).comap (Z1 ρ).subtype).map (Submodule.mkQ _), ?_⟩
  ext z
  constructor
  · rintro ⟨hz, y, hy, e⟩
    have e' : y.1 - z ∈ B1 ρ := (Submodule.Quotient.eq ((B1 ρ).comap (Z1 ρ).subtype)).1 e
    have := N.sub_mem hy (h1 e')
    simpa using this
  · intro hz
    exact ⟨(Zl_iff ρ z).1 (h2 hz), ⟨z, _⟩, hz, rfl⟩

private def Conc {R R' Γ M M' W : Type} [CommRing R] [CommRing R'] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] [Fintype W] {D : W → Type} [∀ w, Group (D w)] [∀ w, TopologicalSpace (D w)]
    (ρ : Representation R Γ M) (ρ' : Representation R' Γ M') (ι : ∀ w, D w →* Γ) (a : ℕ) : Prop :=
  ∀ 𝓛 : ∀ w, AddSubgroup (D w → M),
    (∀ w, (Bl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup ≤ 𝓛 w ∧
      𝓛 w ≤ (Zl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup) →
    Finite (Zl ρ) ∧ Finite (Zl ρ') ∧
    {z | z ∈ Zl ρ ∧ ∀ w, z ∘ ι w ∈ 𝓛 w}.ncard * Nat.card (Bl ρ') * Nat.card M ^ Fintype.card W * a ≤
      Nat.card M * {y | y ∈ Zl ρ' ∧ ∀ w, 𝓛 w = (Zl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup →
        y ∘ ι w ∈ Bl (ρ'.comp (ι w) : Representation R' (D w) M')}.ncard * ∏ w, Nat.card (𝓛 w)

private theorem conc_core {n : ℕ} {Γ M M' W : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module (ZMod n) M]
    [AddCommGroup M'] [Module (ZMod n) M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
    [Finite M] [Finite M'] [Fintype W] {D : W → Type} [∀ w, Group (D w)] [∀ w, TopologicalSpace (D w)]
    (ρ : Representation (ZMod n) Γ M) (ρ' : Representation (ZMod n) Γ M') (ι : ∀ w, D w →* Γ) (hι : ∀ w, Continuous (ι w))
    (a : ℕ) (h : ContAction ρ) (h' : ContAction ρ') [Finite (H1 ρ)] [Finite (H1 ρ')]
    (P : LocCond ρ ι → LocCond ρ' ι) (hP : ∀ L w, L w = ⊤ → ∀ y ∈ P L w, y = 0)
    (gw : ∀ L, Nat.card (Sel ρ ι hι L) * (∏ w, Nat.card (H0 (ρ.comp (ι w)))) * a ≤
      Nat.card (Sel ρ' ι hι (P L)) * Nat.card (H0 ρ) * ∏ w, Nat.card (L w)) : Conc ρ ρ' ι a := by
  intro 𝓛 h𝓛
  have f' := fin_Zl ρ'
  refine ⟨fin_Zl ρ, f', ?_⟩
  choose L hL using fun w => ex_cls (ρ.comp (ι w)) (𝓛 w) (h𝓛 w).1 (h𝓛 w).2
  have e1 : {z | z ∈ Zl ρ ∧ ∀ w, z ∘ ι w ∈ 𝓛 w} = cls ρ (Sel ρ ι hι L) := by
    ext z
    constructor
    · rintro ⟨hz, hw⟩
      refine ⟨(Zl_iff ρ z).1 hz, (mem_Sel _ _ _ _ _).2 fun w => ?_⟩
      have : z ∘ ι w ∈ cls (ρ.comp (ι w)) (L w) := by rw [hL]; exact hw w
      exact this.2
    · rintro ⟨hz, hw⟩
      refine ⟨(Zl_iff ρ z).2 hz, fun w => ?_⟩
      have : z ∘ ι w ∈ cls (ρ.comp (ι w)) (L w) := ⟨(restrictCocycles1 ρ (ι w) (hι w) ⟨z, hz⟩).2, (mem_Sel _ _ _ _ _).1 hw w⟩
      rwa [hL] at this
  have e2 : cls ρ' (Sel ρ' ι hι (P L)) ⊆ {y | y ∈ Zl ρ' ∧ ∀ w,
      𝓛 w = (Zl (ρ.comp (ι w) : Representation (ZMod n) (D w) M)).toAddSubgroup →
        y ∘ ι w ∈ Bl (ρ'.comp (ι w) : Representation (ZMod n) (D w) M')} := by
    rintro y ⟨hy, hw⟩
    refine ⟨(Zl_iff ρ' y).2 hy, fun w e => ?_⟩
    have ht : L w = ⊤ := eq_top_iff.2 fun x _ => by
      induction x using Submodule.Quotient.induction_on with | H x =>
      have : x.1 ∈ cls (ρ.comp (ι w)) (L w) := by rw [hL, e]; exact (Zl_iff _ _).2 x.2
      exact this.2
    have h0 := hP L w ht _ ((mem_Sel _ _ _ _ _).1 hw w)
    exact (Submodule.Quotient.mk_eq_zero ((B1 (ρ'.comp (ι w))).comap (Z1 (ρ'.comp (ι w))).subtype)).1 h0
  have e3 := Set.ncard_le_ncard e2 ((Set.toFinite (Zl ρ' : Set (Γ → M'))).subset fun y hy => hy.1)
  have e4 : ∀ w, Nat.card (𝓛 w) = Nat.card (B1 (ρ.comp (ι w))) * Nat.card (L w) := fun w => by
    rw [← card_cls _ (h.comp' (hι w)), hL]; rfl
  have e5 : Nat.card M ^ Fintype.card W =
      (∏ w, Nat.card (B1 (ρ.comp (ι w)))) * ∏ w, Nat.card (H0 (ρ.comp (ι w))) := by
    rw [← Finset.prod_mul_distrib]
    simp only [card_coboundaries_mul_card_h0, Finset.prod_const, Finset.card_univ]
  rw [card_cls _ h'] at e3
  rw [e1, card_cls _ h, e5]
  simp only [e4, Finset.prod_mul_distrib]
  refine le_trans ?_ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ e3))
  have e6 := Nat.mul_le_mul_left (Nat.card (B1 ρ) * Nat.card (B1 ρ') * ∏ w, Nat.card (B1 (ρ.comp (ι w)))) (gw L)
  rw [← card_coboundaries_mul_card_h0 ρ]
  change _ * _ * Nat.card (B1 ρ') * _ * _ ≤ _
  convert e6 using 1 <;> ring

section Transport

variable {R₁ R₂ G₁ G₂ M₁ M₂ : Type} [CommRing R₁] [CommRing R₂] [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
  [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup M₂] [Module R₂ M₂]

private def tr (e : G₁ ≃ₜ* G₂) (β : M₁ ≃+ M₂) : (G₁ → M₁) ≃+ (G₂ → M₂) where
  toFun z := fun g => β (z (e.symm g))
  invFun z := fun g => β.symm (z (e g))
  left_inv z := by funext g; simp
  right_inv z := by funext g; simp
  map_add' z z' := by funext g; simp

variable {ρ₁ : Representation R₁ G₁ M₁} {ρ₂ : Representation R₂ G₂ M₂} {e : G₁ ≃ₜ* G₂} {β : M₁ ≃+ M₂}

private theorem transport_cocycle_mem (h : ∀ g m, β (ρ₁ g m) = ρ₂ (e g) (β m)) {z : G₁ → M₁} (hz : z ∈ Zl ρ₁) : tr e β z ∈ Zl ρ₂ := by
  refine ⟨(hz.1.comp β).comp_continuous e.symm.continuous, fun g g' => ?_⟩
  change β (z (e.symm (g * g'))) = β (z (e.symm g)) + ρ₂ g (β (z (e.symm g')))
  rw [map_mul, hz.2, map_add, h, e.apply_symm_apply]

private theorem transport_coboundary_mem (h : ∀ g m, β (ρ₁ g m) = ρ₂ (e g) (β m)) {z : G₁ → M₁} (hz : z ∈ Bl ρ₁) : tr e β z ∈ Bl ρ₂ := by
  obtain ⟨m, hm⟩ := (mem_Bl _).1 hz
  refine (mem_Bl _).2 ⟨β m, fun g => ?_⟩
  change β (z (e.symm g)) = _
  rw [hm, map_sub, h, e.apply_symm_apply]

private theorem tr_sym (h : ∀ g m, β (ρ₁ g m) = ρ₂ (e g) (β m)) (g : G₂) (m : M₂) :
    β.symm (ρ₂ g m) = ρ₁ (e.symm g) (β.symm m) := by
  rw [β.symm_apply_eq, h, e.apply_symm_apply, β.apply_symm_apply]

private theorem tr_Zl (h : ∀ g m, β (ρ₁ g m) = ρ₂ (e g) (β m)) (z : G₁ → M₁) : tr e β z ∈ Zl ρ₂ ↔ z ∈ Zl ρ₁ :=
  ⟨fun hz => by
    have := transport_cocycle_mem (tr_sym h) hz
    rwa [show tr e.symm β.symm (tr e β z) = z from (tr e β).symm_apply_apply z] at this, transport_cocycle_mem h⟩

private theorem tr_Bl (h : ∀ g m, β (ρ₁ g m) = ρ₂ (e g) (β m)) (z : G₁ → M₁) : tr e β z ∈ Bl ρ₂ ↔ z ∈ Bl ρ₁ :=
  ⟨fun hz => by
    have := transport_coboundary_mem (tr_sym h) hz
    rwa [show tr e.symm β.symm (tr e β z) = z from (tr e β).symm_apply_apply z] at this, transport_coboundary_mem h⟩

end Transport

private theorem conc_congr {R₁ R₁' Γ₁ M₁' W₁ R₂ R₂' Γ₂ M₂' W₂ M : Type} [AddCommGroup M]
    [CommRing R₁] [CommRing R₁'] [Group Γ₁] [TopologicalSpace Γ₁] [Module R₁ M]
    [AddCommGroup M₁'] [Module R₁' M₁'] [Fintype W₁] {D₁ : W₁ → Type} [∀ w, Group (D₁ w)] [∀ w, TopologicalSpace (D₁ w)]
    [CommRing R₂] [CommRing R₂'] [Group Γ₂] [TopologicalSpace Γ₂] [Module R₂ M]
    [AddCommGroup M₂'] [Module R₂' M₂'] [Fintype W₂] {D₂ : W₂ → Type} [∀ w, Group (D₂ w)] [∀ w, TopologicalSpace (D₂ w)]
    (ρ₁ : Representation R₁ Γ₁ M) (ρ₁' : Representation R₁' Γ₁ M₁') (ι₁ : ∀ w, D₁ w →* Γ₁)
    (ρ₂ : Representation R₂ Γ₂ M) (ρ₂' : Representation R₂' Γ₂ M₂') (ι₂ : ∀ w, D₂ w →* Γ₂) (a : ℕ)
    (e : Γ₁ ≃ₜ* Γ₂) (β : M₁' ≃+ M₂') (σ : W₁ ≃ W₂) (α : ∀ w, D₂ (σ w) ≃ₜ* D₁ w)
    (h : ∀ g m, ρ₁ g m = ρ₂ (e g) m) (h' : ∀ g m, β (ρ₁' g m) = ρ₂' (e g) (β m))
    (hι : ∀ w g, ι₂ (σ w) g = e (ι₁ w (α w g))) (H : Conc ρ₁ ρ₁' ι₁ a) : Conc ρ₂ ρ₂' ι₂ a := by
  intro 𝓛 h𝓛
  let i := AddEquiv.refl M
  have hi : ∀ g m, i (ρ₁ g m) = ρ₂ (e g) (i m) := h
  have l1 : ∀ w g m, i ((ρ₁.comp (ι₁ w) : Representation R₁ (D₁ w) M) g m) =
      (ρ₂.comp (ι₂ (σ w)) : Representation R₂ (D₂ (σ w)) M) ((α w).symm g) (i m) := fun w g m => by
    simp only [MonoidHom.comp_apply, hι, ContinuousMulEquiv.apply_symm_apply]; exact h _ _
  have l2 : ∀ w g m, β ((ρ₁'.comp (ι₁ w) : Representation R₁' (D₁ w) M₁') g m) =
      (ρ₂'.comp (ι₂ (σ w)) : Representation R₂' (D₂ (σ w)) M₂') ((α w).symm g) (β m) := fun w g m => by
    simp only [MonoidHom.comp_apply, hι, ContinuousMulEquiv.apply_symm_apply]; exact h' _ _
  have c1 : ∀ w (z : Γ₁ → M), tr e i z ∘ ι₂ (σ w) = tr (α w).symm i (z ∘ ι₁ w) := fun w z => by
    funext g
    change i (z (e.symm (ι₂ (σ w) g))) = i (z (ι₁ w (α w g)))
    rw [hι, e.symm_apply_apply]
  have c2 : ∀ w (z : Γ₁ → M₁'), tr e β z ∘ ι₂ (σ w) = tr (α w).symm β (z ∘ ι₁ w) := fun w z => by
    funext g
    change β (z (e.symm (ι₂ (σ w) g))) = β (z (ι₁ w (α w g)))
    rw [hι, e.symm_apply_apply]
  let 𝓚 : ∀ w, AddSubgroup (D₁ w → M) := fun w => (𝓛 (σ w)).comap (tr (α w).symm i).toAddMonoidHom
  have hK : ∀ w z, z ∈ 𝓚 w ↔ tr (α w).symm i z ∈ 𝓛 (σ w) := fun _ _ => Iff.rfl
  obtain ⟨f1, f2, H⟩ := H 𝓚 fun w =>
    ⟨fun z hz => (h𝓛 _).1 ((tr_Bl (l1 w) z).2 hz), fun z hz => (tr_Zl (l1 w) z).1 ((h𝓛 _).2 hz)⟩
  refine ⟨Finite.of_equiv _ ((tr e i).toEquiv.subtypeEquiv fun z => (tr_Zl hi z).symm),
    Finite.of_equiv _ ((tr e β).toEquiv.subtypeEquiv fun z => (tr_Zl h' z).symm), ?_⟩
  have e1 : {z | z ∈ Zl ρ₁ ∧ ∀ w, z ∘ ι₁ w ∈ 𝓚 w}.ncard = {z | z ∈ Zl ρ₂ ∧ ∀ w, z ∘ ι₂ w ∈ 𝓛 w}.ncard := by
    refine Set.ncard_congr (fun z _ => tr e i z) ?_ (fun _ _ _ _ h => (tr e i).injective h) ?_
    · rintro z ⟨hz, hw⟩
      refine ⟨(tr_Zl hi z).2 hz, σ.surjective.forall.2 fun w => ?_⟩
      rw [c1]; exact hw w
    · intro z hz
      obtain ⟨z, rfl⟩ := (tr e i).surjective z
      refine ⟨z, ⟨(tr_Zl hi z).1 hz.1, fun w => ?_⟩, rfl⟩
      rw [hK, ← c1]; exact hz.2 _
  have e2 : Nat.card (Bl ρ₁') = Nat.card (Bl ρ₂') :=
    Nat.card_congr ((tr e β).toEquiv.subtypeEquiv fun z => (tr_Bl h' z).symm)
  have e3 : ∏ w, Nat.card (𝓚 w) = ∏ w, Nat.card (𝓛 w) :=
    Fintype.prod_equiv σ _ _ fun w => Nat.card_congr ((tr (α w).symm i).toEquiv.subtypeEquiv (hK w))
  have e4 : ∀ w, 𝓚 w = (Zl (ρ₁.comp (ι₁ w) : Representation R₁ (D₁ w) M)).toAddSubgroup ↔
      𝓛 (σ w) = (Zl (ρ₂.comp (ι₂ (σ w)) : Representation R₂ (D₂ (σ w)) M)).toAddSubgroup := fun w => by
    simp only [AddSubgroup.ext_iff, Submodule.mem_toAddSubgroup]
    rw [(tr (α w).symm i).surjective.forall]
    exact forall_congr' fun z => by rw [hK, tr_Zl (l1 w)]
  have e5 : {y | y ∈ Zl ρ₁' ∧ ∀ w, 𝓚 w = (Zl (ρ₁.comp (ι₁ w) : Representation R₁ (D₁ w) M)).toAddSubgroup →
        y ∘ ι₁ w ∈ Bl (ρ₁'.comp (ι₁ w) : Representation R₁' (D₁ w) M₁')}.ncard =
      {y | y ∈ Zl ρ₂' ∧ ∀ w, 𝓛 w = (Zl (ρ₂.comp (ι₂ w) : Representation R₂ (D₂ w) M)).toAddSubgroup →
        y ∘ ι₂ w ∈ Bl (ρ₂'.comp (ι₂ w) : Representation R₂' (D₂ w) M₂')}.ncard := by
    refine Set.ncard_congr (fun z _ => tr e β z) ?_ (fun _ _ _ _ h => (tr e β).injective h) ?_
    · rintro z ⟨hz, hw⟩
      refine ⟨(tr_Zl h' z).2 hz, σ.surjective.forall.2 fun w hL => ?_⟩
      rw [c2, tr_Bl (l2 w)]; exact hw w ((e4 w).2 hL)
    · intro z hz
      obtain ⟨z, rfl⟩ := (tr e β).surjective z
      refine ⟨z, ⟨(tr_Zl h' z).1 hz.1, fun w hL => ?_⟩, rfl⟩
      rw [← tr_Bl (l2 w), ← c2]; exact hz.2 _ ((e4 w).1 hL)
  rwa [e1, e2, e3, e5, Fintype.card_congr σ] at H

private theorem cup_inj {R Γ D M : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    [Group Γ] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ)
    (hρ : ContAction (ρ.comp φ)) (χ' : D →* Rˣ) (e : χ' = χ.comp φ)
    (h : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) (hρ.comp' continuous_id))) :
    Function.Injective (cupH1H1TwistedDual χ ρ φ hρ) := by
  subst e
  have e1 : (twDual χ ρ).comp φ = (twDual (χ.comp φ) (ρ.comp φ)).comp (MonoidHom.id D) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun y => TDual.ext fun m => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply, map_inv φ]
  have gen : ∀ (σ σ' : Representation R D (TDual R M)) (_ : σ = σ') h1 h2,
      Function.Injective (cupProductH1H1 σ' (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h2 hρ) →
      Function.Injective (cupProductH1H1 σ (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h1 hρ) := by
    intro σ σ' e h1 h2 h
    subst e
    exact h
  exact gen _ _ e1 _ (fun g y x => evalPair_equiv (χ.comp φ) (ρ.comp φ) g x y) h

private theorem ex_dual (N : ℕ) [NeZero N] (M M' : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M]
    [AddCommGroup M'] [Finite M'] (b : M →+ M' →+ ZMod N) (hl : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hr : ∀ y, (∀ x, b x y = 0) → y = 0) : ∃ β : M' ≃+ TDual (ZMod N) M, ∀ y x, β y x = b x y := by
  letI : Module (ZMod N) M' := AddCommGroup.zmodModule fun y => hr _ fun x => by
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let f : M' →+ TDual (ZMod N) M :=
    { toFun := fun y => TDual.mk ((b.flip y).toZModLinearMap N)
      map_zero' := TDual.ext fun x => map_zero (b x)
      map_add' := fun y y' => TDual.ext fun x => map_add (b x) y y' }
  have hf : Function.Bijective f := (UpperTheory.V.Th.dualZ N M).2.2 M' b hl hr
  exact ⟨AddEquiv.ofBijective f hf, fun _ _ => rfl⟩

private def zrep (n : ℕ) {R Γ Γ' M : Type} [CommRing R] [Group Γ] [Group Γ'] [AddCommGroup M] [Module R M]
    [Module (ZMod n) M] (ρ : Representation R Γ M) (e : Γ' →* Γ) : Representation (ZMod n) Γ' M where
  toFun g := (ρ (e g)).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    change ρ (e 1) m = m
    simp
  map_mul' g h := LinearMap.ext fun m => by
    change ρ (e (g * h)) m = ρ (e g) (ρ (e h) m)
    simp

end Helpers

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.gwCntBare :
    GreenbergWiles → LocalTateDuality → GlobalFiniteness → LocalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (e : GS Ω S ≃ₜ* Γ) (ε : Γ →* ℤ_[l]ˣ) (W : Type) [Fintype W] (pl : W ≃ S) (A : W → ValuationSubring Ω) (D : W → Type) [∀ w, Group (D w)] [∀ w, TopologicalSpace (D w)] (ι : ∀ w, D w →* Γ) (α : ∀ w, D w ≃ₜ* Dec (F := F) (A w)) (d : ℕ) (ip : Fin d ≃ InfinitePlace F) (c : Fin d → G F Ω), l ≠ 2 → (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → (∀ g, ε (e (toGS Ω S g)) = cycZ F Ω l g) → (∀ w, IsPlaceOver (A w) (pl w).1) → (∀ w g, ι w g = e (toGS Ω S (α w g : G F Ω))) → (∀ i, IsCCAt (ip i) (c i)) → GWCnt ε D ι fun i => e (toGS Ω S (c i)) := by
  classical
  intro hGW hT hGF _ l _ F Ω _ _ _ _ _ _ S Γ _ _ _ e ε W _ pl A D _ _ ι α d ip c hl hS hε hA hι hc
  obtain ⟨T, rfl⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), (T : Set _) = S :=
    ⟨(Set.finite_coe_iff.1 (Finite.of_equiv W pl)).toFinset, Set.Finite.coe_toFinset _⟩
  intro k hk0 R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hb
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hk : ∀ x : M, l ^ k • x = 0 := fun x => hb.left _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ k)) M) := ⟨AddCommGroup.zmodModule hk⟩
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  let ρS : Representation (ZMod (l ^ k)) (GS Ω (T : Set (HeightOneSpectrum (𝓞 F)))) M :=
    zrep (l ^ k) ρ e.toMulEquiv.toMonoidHom
  have hρS : ∀ g m, ρS g m = ρ (e g) m := fun _ _ => rfl
  have hcont : ContAction ρS :=
    continuous_prod_of_discrete_right.2 fun m => (hLC m).continuous.comp e.continuous
  have hT' : ContainsAbove T l := hS
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := k) (S := T) hT'
  have hcont' : ContAction (twDual μ ρS) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hcont
  have hμε : ∀ g, ((μ g : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) = PadicInt.toZModPow k ((ε (e g) : ℤ_[l]ˣ) : ℤ_[l]) := fun g => by
    obtain ⟨g, rfl⟩ : ∃ s, toGS Ω _ s = g := QuotientGroup.mk_surjective g
    rw [hε, ← MonoidHom.comp_apply, hμ]
    rfl
  obtain ⟨β, hβ'⟩ := ex_dual (l ^ k) M M' b hb.left hb.right
  have heq : ∀ g φ, β.symm (twDual μ ρS g φ) = ρ' (e g) (β.symm φ) := fun g φ => by
    obtain ⟨y, rfl⟩ := β.surjective φ
    rw [β.symm_apply_apply, β.symm_apply_eq]
    refine TDual.ext fun m => ?_
    rw [twDual_apply, hβ', hβ', hμε, ← hb.equiv, hρS, map_inv e, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  let σ : T ≃ W := pl.symm
  let Av : T → ValuationSubring Ω := fun v => A (σ v)
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := fun v => by
    have := hA (σ v)
    rwa [show pl (σ v) = v from pl.apply_symm_apply v] at this
  haveI : Finite (TDual (ZMod (l ^ k)) M) := GlobalTheory.DualSide.finite_TDual
  haveI := (hGF F Ω l k M T ρS hk0 hT' hcont).2.1
  haveI := (hGF F Ω l k _ T (twDual μ ρS) hk0 hT' hcont').2.1
  have key : ∀ v : T, Function.Injective (cupH1H1TwistedDual μ ρS (locFam T Av v) (hcont.comp' (continuous_locFam T Av v))) := fun v =>
    cup_inj μ ρS _ _ _ (by rw [← hμ]; rfl) (hT F Ω l k M (Av v) (ρS.comp (locFam T Av v)) v.1 hk0 (hAv v)
      (hcont.comp' (continuous_locFam T Av v))).2.2.1.1
  have harch : archH0Card T ρS (fun w => c (ip.symm w)) =
      ∏ i, Nat.card {m : M // ρ (e (toGS Ω _ (c i))) m = m} := by
    rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
      Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w]
    exact Fintype.prod_equiv ip.symm _ _ fun w => rfl
  refine conc_congr ρS (twDual μ ρS) (locFam T Av) ρ ρ' ι _ e β.symm σ (fun v => α (σ v)) hρS heq
    (fun v g => hι _ g) ?_
  refine conc_core ρS (twDual μ ρS) (locFam T Av) (continuous_locFam T Av) _ hcont hcont'
    (perpCond μ ρS (locFam T Av) fun v => hcont.comp' (continuous_locFam T Av v)) (fun L v hL y hy => key v ?_) fun L => ?_
  · rw [map_zero]
    exact LinearMap.ext fun x => (mem_perpCond _ _ _ _ _ _ _).1 hy x (hL ▸ Submodule.mem_top)
  · have h := hGW F Ω l k M T ρS hk0 hl hT' hcont μ hμ Av hAv (fun w => c (ip.symm w))
      (fun w _ => by simpa using hc (ip.symm w)) L
    rw [← h, harch]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ Nat.card_pos))
