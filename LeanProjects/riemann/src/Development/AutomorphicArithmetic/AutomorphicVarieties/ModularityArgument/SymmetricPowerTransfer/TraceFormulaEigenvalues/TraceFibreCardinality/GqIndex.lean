import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

open MulAction

section

variable {H' H Y : Type} [Group H'] [Group H] [MulAction H Y] [MulAction H' Y]

private theorem orb_iff (φ : H' →* H) (hφ : ∀ (a : H') (y : Y), a • y = φ a • y) (H₀ : Subgroup H) [H₀.Normal]
    (h0 : ∀ z ∈ H₀, ∀ y : Y, z • y = y) (y y' : Y) :
    (Quotient.mk (orbitRel H' Y) y = Quotient.mk (orbitRel H' Y) y') ↔ ∃ c ∈ φ.range ⊔ H₀, c • y' = y := by
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, Subgroup.mem_sup_left ⟨a, rfl⟩, (hφ a y').symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨_, ⟨a, rfl⟩, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hc
    exact ⟨a, by rw [hφ, mul_smul, h0 z hz]⟩

private theorem w_mul (φ : H' →* H) (hφ : ∀ (a : H') (y : Y), a • y = φ a • y) (H₀ : Subgroup H) [H₀.Normal]
    (h0 : ∀ z ∈ H₀, ∀ y : Y, z • y = y) (y : Y) :
    (H₀.comap φ).relIndex (stabilizer H' y) * (φ.range ⊔ H₀).relIndex (stabilizer H y) = H₀.relIndex (stabilizer H y) := by
  have hH₀S : H₀ ≤ stabilizer H y := fun z hz => h0 z hz y
  have hS' : stabilizer H' y = (stabilizer H y).comap φ := by
    ext a
    simp [mem_stabilizer_iff, hφ]
  have hdk : (φ.range ⊔ H₀) ⊓ stabilizer H y = (φ.range ⊓ stabilizer H y) ⊔ H₀ := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_sup_of_normal_right]
    constructor
    · rintro ⟨⟨p, hp, z, hz, rfl⟩, hx⟩
      refine ⟨p, ⟨hp, ?_⟩, z, hz, rfl⟩
      have hpz : p = (p * z) * z⁻¹ := by group
      rw [hpz]
      exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hH₀S hz))
    · rintro ⟨p, ⟨hp, hpS⟩, z, hz, rfl⟩
      exact ⟨⟨p, hp, z, hz, rfl⟩, Subgroup.mul_mem _ hpS (hH₀S hz)⟩
  rw [hS', Subgroup.relIndex_comap, Subgroup.map_comap_eq,
    ← Subgroup.relIndex_sup_right (φ.range ⊓ stabilizer H y) H₀, ← hdk,
    ← Subgroup.inf_relIndex_right (φ.range ⊔ H₀) (stabilizer H y)]
  exact Subgroup.relIndex_mul_relIndex _ _ _ (le_inf le_sup_right hH₀S) inf_le_right

private theorem fib_card (K : Subgroup H) (g : H) (y : Y) :
    {x : H ⧸ K | ∃ c ∈ K, c • y = x.out⁻¹ • g • y}.ncard = K.relIndex (stabilizer H y) := by
  classical
  let f : stabilizer H y ⧸ K.subgroupOf (stabilizer H y) → H ⧸ K :=
    Quotient.map' (fun s : stabilizer H y => g * (s : H)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      rw [Subgroup.mem_subgroupOf] at hab
      simpa [mul_assoc] using hab)
  have hf : ∀ s : stabilizer H y, f (QuotientGroup.mk s) = QuotientGroup.mk (g * (s : H)) := fun s => rfl
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hf, hf, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hab
  have hrange : {x : H ⧸ K | ∃ c ∈ K, c • y = x.out⁻¹ • g • y} = Set.range f := by
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k0, hout⟩ := QuotientGroup.mk_out_eq_mul K h
    simp only [Set.mem_setOf_eq, Set.mem_range, hout]
    constructor
    · rintro ⟨c, hc, hcy⟩
      have hs : g⁻¹ * (h * k0 * c) ∈ stabilizer H y := by
        rw [mem_stabilizer_iff, mul_smul, mul_smul, hcy, ← mul_smul, ← mul_smul]
        simp only [mul_inv_rev]
        rw [← mul_smul, show g⁻¹ * (h * (k0 : H)) * ((k0 : H)⁻¹ * h⁻¹) * g = 1 by group, one_smul]
      refine ⟨QuotientGroup.mk ⟨g⁻¹ * (h * k0 * c), hs⟩, ?_⟩
      rw [hf, QuotientGroup.eq]
      have hm : (c⁻¹ * (k0 : H)⁻¹) ∈ K := K.mul_mem (K.inv_mem hc) (K.inv_mem k0.2)
      simpa [mul_assoc] using hm
    · rintro ⟨q, hq⟩
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hf, QuotientGroup.eq] at hq
      refine ⟨(h * k0)⁻¹ * (g * s), ?_, ?_⟩
      · have hm := K.mul_mem (K.inv_mem k0.2) (K.inv_mem hq)
        simpa [mul_assoc] using hm
      · rw [mul_smul, mul_smul, mem_stabilizer_iff.mp s.2]
  rw [hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
  rfl

private theorem w_conj (H₀ : Subgroup H) [hN : H₀.Normal] (g : H) (y : Y) :
    H₀.relIndex (stabilizer H (g • y)) = H₀.relIndex (stabilizer H y) := by
  have hmap : H₀.map (MulAut.conj g).toMonoidHom = H₀ := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hN.conj_mem a ha g
    · intro hx
      exact ⟨g⁻¹ * x * g, by simpa using hN.conj_mem x hx g⁻¹, by simp [mul_assoc]⟩
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← hmap]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

private theorem gq_index (φ : H' →* H) (hφ : ∀ (a : H') (y : Y), a • y = φ a • y) (H₀ : Subgroup H) [H₀.Normal]
    (h0 : ∀ z ∈ H₀, ∀ y : Y, z • y = y) (k : Y → ℂ) (hn : (φ.range ⊔ H₀).index ≠ 0) (hk : ∀ (h : H) y, k (h • y) = k y)
    (hS : ∃ S : Finset Y, ∀ y, k y ≠ 0 → ∃ h : H, ∃ x ∈ S, y = h • x)
    (hw : ∀ y, k y ≠ 0 → H₀.relIndex (stabilizer H y) ≠ 0) :
    gq (H₀.comap φ) k = ((φ.range ⊔ H₀).index : ℂ) * gq H₀ k := by
  classical
  haveI : (φ.range ⊔ H₀).FiniteIndex := ⟨hn⟩
  letI : Fintype (H ⧸ (φ.range ⊔ H₀)) := Fintype.ofFinite _
  obtain ⟨S0, hS0⟩ := hS
  let π : orbitRel.Quotient H' Y → orbitRel.Quotient H Y := fun q' => Quotient.mk (orbitRel H Y) q'.out
  let T : orbitRel.Quotient H Y → ℂ := fun q =>
    k q.out / (H₀.relIndex (stabilizer H q.out) : ℂ)
  let T' : orbitRel.Quotient H' Y → ℂ := fun q' =>
    k q'.out / ((H₀.comap φ).relIndex (stabilizer H' q'.out) : ℂ)
  have hgq : gq H₀ k = ∑ᶠ q, T q := rfl
  have hgq' : gq (H₀.comap φ) k = ∑ᶠ q', T' q' := rfl
  have mkH_smul : ∀ (h : H) (y : Y), Quotient.mk (orbitRel H Y) (h • y) = Quotient.mk (orbitRel H Y) y := by
    intro h y
    exact Quotient.sound (orbitRel_apply.mpr ⟨h, rfl⟩)
  have mkH_of : ∀ a b : Y, Quotient.mk (orbitRel H' Y) a = Quotient.mk (orbitRel H' Y) b →
      Quotient.mk (orbitRel H Y) a = Quotient.mk (orbitRel H Y) b := by
    intro a b hab
    obtain ⟨c, -, hc⟩ := (orb_iff φ hφ H₀ h0 a b).mp hab
    rw [← hc, mkH_smul]
  have hsame : ∀ q', ∃ h : H, (π q').out = h • q'.out := by
    intro q'
    have e : Quotient.mk (orbitRel H Y) (π q').out = Quotient.mk (orbitRel H Y) q'.out := Quotient.out_eq _
    obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact e))
    exact ⟨h, hh.symm⟩
  have hT' : ∀ q', T' q' = T (π q') * ((φ.range ⊔ H₀).relIndex (stabilizer H q'.out) : ℂ) := by
    intro q'
    obtain ⟨h, hh⟩ := hsame q'
    show k q'.out / ((H₀.comap φ).relIndex (stabilizer H' q'.out) : ℂ) =
      k (π q').out / (H₀.relIndex (stabilizer H (π q').out) : ℂ) *
        ((φ.range ⊔ H₀).relIndex (stabilizer H q'.out) : ℂ)
    rw [hh, hk, w_conj]
    by_cases hk0 : k q'.out = 0
    · simp [hk0]
    · have hw0 := hw _ hk0
      have hm := w_mul φ hφ H₀ h0 q'.out
      rw [← hm] at hw0 ⊢
      have h1 : ((H₀.comap φ).relIndex (stabilizer H' q'.out) : ℂ) ≠ 0 := by
        exact_mod_cast left_ne_zero_of_mul hw0
      have h2 : ((φ.range ⊔ H₀).relIndex (stabilizer H q'.out) : ℂ) ≠ 0 := by
        exact_mod_cast right_ne_zero_of_mul hw0
      push_cast
      field_simp
  let Q0 : Finset (orbitRel.Quotient H Y) := S0.image (fun s => Quotient.mk (orbitRel H Y) s)
  let Q0' : Finset (orbitRel.Quotient H' Y) :=
    (S0 ×ˢ (Finset.univ : Finset (H ⧸ (φ.range ⊔ H₀)))).image
      (fun p => Quotient.mk (orbitRel H' Y) (p.2.out⁻¹ • p.1))
  have inQ0' : ∀ s ∈ S0, ∀ h : H, Quotient.mk (orbitRel H' Y) (h • s) ∈ Q0' := by
    intro s hs h
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (φ.range ⊔ H₀) h⁻¹
    refine Finset.mem_image.mpr ⟨(s, QuotientGroup.mk h⁻¹), Finset.mem_product.mpr ⟨hs, Finset.mem_univ _⟩, ?_⟩
    show Quotient.mk (orbitRel H' Y) ((QuotientGroup.mk h⁻¹ : H ⧸ (φ.range ⊔ H₀)).out⁻¹ • s) =
      Quotient.mk (orbitRel H' Y) (h • s)
    rw [orb_iff φ hφ H₀ h0]
    refine ⟨(l : H)⁻¹, Subgroup.inv_mem _ l.2, ?_⟩
    rw [hl, mul_inv_rev, inv_inv, mul_smul]
  have hsuppT : Function.support T ⊆ ↑Q0 := by
    intro q hq
    have hk0 : k q.out ≠ 0 := by
      intro h
      exact hq (by simp [T, h])
    obtain ⟨h, x, hx, hxq⟩ := hS0 _ hk0
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, ?_⟩)
    rw [← mkH_smul h x, ← hxq, Quotient.out_eq]
  have hsuppT' : Function.support T' ⊆ ↑Q0' := by
    intro q' hq'
    have hk0 : k q'.out ≠ 0 := by
      intro h
      exact hq' (by simp [T', h])
    obtain ⟨h, x, hx, hxq⟩ := hS0 _ hk0
    have := inQ0' x hx h
    rw [← hxq, Quotient.out_eq] at this
    exact Finset.mem_coe.mpr this
  have hmaps : ∀ q' ∈ Q0', π q' ∈ Q0 := by
    intro q' hq'
    obtain ⟨⟨s, x⟩, hp, rfl⟩ := Finset.mem_image.mp hq'
    refine Finset.mem_image.mpr ⟨s, (Finset.mem_product.mp hp).1, ?_⟩
    show Quotient.mk (orbitRel H Y) s = Quotient.mk (orbitRel H Y)
      (Quotient.mk (orbitRel H' Y) (x.out⁻¹ • s)).out
    rw [mkH_of _ (x.out⁻¹ • s) (Quotient.out_eq _), mkH_smul]
  have hfib : ∀ q ∈ Q0, ∑ q' ∈ Q0' with π q' = q,
      ((φ.range ⊔ H₀).relIndex (stabilizer H q'.out) : ℂ) = ((φ.range ⊔ H₀).index : ℂ) := by
    intro q hq
    obtain ⟨s, hs, hsq⟩ := Finset.mem_image.mp hq
    let Φ : H ⧸ (φ.range ⊔ H₀) → orbitRel.Quotient H' Y := fun x => Quotient.mk (orbitRel H' Y) (x.out⁻¹ • q.out)
    obtain ⟨h1, hh1⟩ : ∃ h1 : H, q.out = h1 • s := by
      have e : Quotient.mk (orbitRel H Y) q.out = Quotient.mk (orbitRel H Y) s := by rw [Quotient.out_eq, hsq]
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact e))
      exact ⟨h, hh.symm⟩
    have hΦ : Set.MapsTo Φ ↑(Finset.univ : Finset (H ⧸ (φ.range ⊔ H₀))) ↑(Q0'.filter (fun q' => π q' = q)) := by
      intro x _
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
      · show Quotient.mk (orbitRel H' Y) (x.out⁻¹ • q.out) ∈ Q0'
        rw [hh1, ← mul_smul]
        exact inQ0' s hs _
      · show Quotient.mk (orbitRel H Y) (Quotient.mk (orbitRel H' Y) (x.out⁻¹ • q.out)).out = q
        rw [mkH_of _ (x.out⁻¹ • q.out) (Quotient.out_eq _), mkH_smul, Quotient.out_eq]
    have hcard := Finset.card_eq_sum_card_fiberwise hΦ
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hcard
    rw [hcard]
    push_cast
    refine Finset.sum_congr rfl fun q' hq' => ?_
    have hπ : π q' = q := (Finset.mem_filter.mp hq').2
    obtain ⟨g, hg⟩ := hsame q'
    rw [hπ] at hg
    have hset : ((Finset.univ.filter (fun x => Φ x = q') : Finset (H ⧸ (φ.range ⊔ H₀))) : Set (H ⧸ (φ.range ⊔ H₀))) =
        {x : H ⧸ (φ.range ⊔ H₀) | ∃ c ∈ φ.range ⊔ H₀, c • q'.out = x.out⁻¹ • g • q'.out} := by
      ext x
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [← orb_iff φ hφ H₀ h0, Quotient.out_eq]
      show Quotient.mk (orbitRel H' Y) (x.out⁻¹ • q.out) = q' ↔ _
      rw [hg]
    rw [← Set.ncard_coe_finset, hset, fib_card]
  rw [hgq', hgq, finsum_eq_sum_of_support_subset T' hsuppT', finsum_eq_sum_of_support_subset T hsuppT,
    ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_congr rfl fun q' hq' => by rw [hT', (Finset.mem_filter.mp hq').2], ← Finset.mul_sum, hfib q hq,
    mul_comm]

end

theorem gqIndex : GqIndex := by
  intro H' H G _ _ _ φ j H₀ U k hN h0 hn hk hS hw
  letI : MulAction H (G ⧸ U) := MulAction.compHom _ j
  letI : MulAction H' (G ⧸ U) := MulAction.compHom _ (j.comp φ)
  exact gq_index φ (fun _ _ => rfl) H₀ h0 k hn hk hS hw

end UpperTheory.V.Z.Sym.Tf
