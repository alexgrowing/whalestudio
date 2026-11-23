import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem dcG_mem {H : Type} [Group H] (K : Subgroup H) (x p : H) :
    (p : H ⧸ K) ∈ MulAction.orbit K (x : H ⧸ K) ↔ ∃ k ∈ K, ∃ k' ∈ K, p = k * x * k' := by
  constructor
  · rintro ⟨k, hk⟩
    have h : (((k : H) * x : H) : H ⧸ K) = (p : H ⧸ K) := hk
    exact ⟨k, k.2, _, QuotientGroup.eq.mp h, by group⟩
  · rintro ⟨k, hk, k', hk', rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    change ((k * x : H) : H ⧸ K) = _
    exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hk')

private theorem dcG_sum {α β γ M : Type} [AddCommMonoid M] [DecidableEq γ] (s : Finset α) (t : Finset β)
    (F : α → γ) (G : β → γ) (g : γ → M)
    (h : ∀ r, (s.filter fun a => F a = r).card = (t.filter fun b => G b = r).card) :
    ∑ a ∈ s, g (F a) = ∑ b ∈ t, g (G b) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image F ∪ t.image G) (g := F)
      (fun a ha => Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)),
    ← Finset.sum_fiberwise_of_maps_to (s := t) (t := s.image F ∪ t.image G) (g := G)
      (fun a ha => Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g r) (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
    Finset.sum_congr rfl (s₁ := t.filter fun b => G b = r) (g := fun _ => g r)
      (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
    Finset.sum_const, Finset.sum_const, h]

open Classical in
private theorem dcG_le {H : Type} [Group H] (K : Subgroup H) (s : H → H)
    (hmul : ∀ x y, s (x * y) = s y * s x) (hss : ∀ x, s (s x) = x) (hK : ∀ k ∈ K, s k ∈ K)
    (hd : ∀ x, ∃ k ∈ K, ∃ k' ∈ K, s x = k * x * k')
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x y : H) (r : H ⧸ K) :
    (((hfin x).toFinset ×ˢ (hfin y).toFinset).filter fun a => a.1.out • a.2 = r).card ≤
      (((hfin y).toFinset ×ˢ (hfin x).toFinset).filter fun a => a.1.out • a.2 = r).card := by
  have h1 : s 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have hinv : ∀ a, s a⁻¹ = (s a)⁻¹ := fun a => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hmul, mul_inv_cancel, h1]
  have hD : ∀ x p : H, (∃ k ∈ K, ∃ k' ∈ K, p = k * x * k') → ∀ a ∈ K, ∀ b ∈ K,
      ∃ k ∈ K, ∃ k' ∈ K, a * s p * b = k * x * k' := by
    rintro x p ⟨k, hk, k', hk', hp⟩ a ha b hb
    obtain ⟨l, hl, l', hl', h⟩ := hd p
    exact ⟨a * l * k, mul_mem (mul_mem ha hl) hk, k' * l' * b, mul_mem (mul_mem hk' hl') hb, by
      rw [h, hp]; group⟩
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective r
  obtain ⟨k, hk, k', hk', hz⟩ := hd z
  let φ : H ⧸ K → H ⧸ K := fun p => ((k⁻¹ * s (p.out⁻¹ * z) * 1 : H) : H ⧸ K)
  refine Finset.card_le_card_of_injOn (fun a => (φ a.1, (φ a.1).out⁻¹ • (z : H ⧸ K))) ?_ ?_
  · rintro ⟨p, q⟩ ha
    simp only [Finset.coe_filter, Finset.mem_product, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨⟨hp, hq⟩, hpq⟩ := ha
    have hq' : q = ((p.out⁻¹ * z : H) : H ⧸ K) := by
      change q = p.out⁻¹ • (z : H ⧸ K)
      rw [← hpq, inv_smul_smul]
    refine ⟨⟨?_, ?_⟩, smul_inv_smul _ _⟩
    · rw [hq', dcG_mem] at hq
      exact (dcG_mem K _ _).mpr (hD _ _ hq _ (inv_mem hk) _ (one_mem _))
    · rw [← QuotientGroup.out_eq' p, dcG_mem] at hp
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (k⁻¹ * s (p.out⁻¹ * z) * 1)
      change (((φ p).out⁻¹ * z : H) : H ⧸ K) ∈ _
      have : (φ p).out⁻¹ * z = (m : H)⁻¹ * s p.out * k'⁻¹ := by
        simp only [φ]
        rw [hm, hmul, hinv, hz]
        group
      rw [this]
      exact (dcG_mem K _ _).mpr (hD _ _ hp _ (inv_mem m.2) _ (inv_mem hk'))
  · rintro ⟨p, q⟩ ha ⟨p', q'⟩ ha' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha ha'
    have h2 : φ p = φ p' := congrArg Prod.fst h
    have h3 := hK _ (QuotientGroup.eq.mp h2)
    have h4 : (k⁻¹ * s (p.out⁻¹ * z) * 1)⁻¹ * (k⁻¹ * s (p'.out⁻¹ * z) * 1) = s (p'.out⁻¹ * p.out) := by
      rw [hmul, hmul, hmul, hinv, hinv]
      group
    rw [h4, hss] at h3
    have h5 : p' = p := by
      rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' p']
      exact QuotientGroup.eq.mpr h3
    subst h5
    have h6 : q = q' := smul_left_cancel p'.out (ha.2.trans ha'.2.symm)
    rw [h6]

private theorem dcG_two {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H)
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x y : H) (v : M) (hv : v ∈ fixd ρ K) :
    dc ρ K K x (dc ρ K K y v) =
      ∑ a ∈ (hfin x).toFinset ×ˢ (hfin y).toFinset, ρ (a.1.out • a.2 : H ⧸ K).out v := by
  have h : ∀ (x : H) (w : M), dc ρ K K x w = ∑ p ∈ (hfin x).toFinset, ρ p.out w := by
    intro x w
    rw [dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ (hfin x),
      LinearMap.sum_apply]
  rw [h, h, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (p.out * q.out)
  have h2 : (p.out • q : H ⧸ K) = ((p.out * q.out : H) : H ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h2, hm, map_mul, map_mul]
  simp only [Module.End.mul_apply]
  rw [hv m m.2]

theorem UpperTheory.V.Hi.dcGelfand :
    ∀ (A H M : Type) [CommRing A] [Group H] [AddCommGroup M] [Module A M] (ρ : Representation A H M) (K : Subgroup H) (s : H → H), (∀ x y, s (x * y) = s y * s x) → (∀ x, s (s x) = x) → (∀ k ∈ K, s k ∈ K) → (∀ x, ∃ k ∈ K, ∃ k' ∈ K, s x = k * x * k') → (∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) → (∀ x : H, (MulAction.orbit K (x : H ⧸ K)).ncard = (MulAction.orbit K ((x⁻¹ : H) : H ⧸ K)).ncard) → ∀ x y, ∀ v ∈ fixd ρ K, dc ρ K K x (dc ρ K K y v) = dc ρ K K y (dc ρ K K x v) := by
  intro A H M _ _ _ _ ρ K s hmul hss hK hd hfin _ x y v hv
  classical
  rw [dcG_two ρ K hfin x y v hv, dcG_two ρ K hfin y x v hv]
  refine dcG_sum _ _ (fun a : (H ⧸ K) × (H ⧸ K) => a.1.out • a.2) (fun a : (H ⧸ K) × (H ⧸ K) => a.1.out • a.2)
    (fun r => ρ r.out v) fun r => ?_
  apply le_antisymm
  · convert dcG_le K s hmul hss hK hd hfin x y r
  · convert dcG_le K s hmul hss hK hd hfin y x r
