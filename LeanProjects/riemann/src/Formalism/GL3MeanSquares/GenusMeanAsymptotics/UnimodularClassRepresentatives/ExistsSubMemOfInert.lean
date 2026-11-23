import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NotIsPrimeMapOfSplit

namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

private theorem exists_sub_iota_mem_of_sub_involution_mem (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P)
    (x : B) (hx : x - σ x ∈ P) : ∃ a : A, x - ι a ∈ P := by
  have hσP : ∀ p ∈ P, σ p ∈ P := fun p hp => Ideal.mem_comap.1 (hc.symm ▸ hp)
  have hσδ : σ (θ - σ θ) = -(θ - σ θ) := by
    rw [map_sub, hσ]
    ring
  have hDP : (θ - σ θ) * (θ - σ θ) ∉ P := fun h => hθ ((hP.isPrime.mem_or_mem h).elim id id)
  obtain ⟨u, i, hi, hui⟩ := hP.exists_inv hDP
  have hσi : σ i ∈ P := hσP i hi
  have h2 : σ u * ((θ - σ θ) * (θ - σ θ)) + σ i = 1 := by
    have := congrArg σ hui
    rwa [map_add, map_mul, map_mul, hσδ, map_one, neg_mul_neg] at this

  set y := ((x * θ - σ x * σ θ) * (θ - σ θ)) * (u * σ u * ((θ - σ θ) * (θ - σ θ))) with hy_def
  have hy : σ y = y := by
    rw [hy_def]
    simp only [map_mul, map_sub, hσ]
    ring
  obtain ⟨a, ha⟩ := (hfix y).1 hy
  refine ⟨a, ?_⟩
  rw [ha]
  have e : x - y = x * i + x * σ i - x * i * σ i -
      (x - σ x) * (σ θ * (θ - σ θ) * u * σ u * ((θ - σ θ) * (θ - σ θ))) := by
    rw [hy_def]
    linear_combination (-x * σ u * ((θ - σ θ) * (θ - σ θ))) * hui + (-x * (1 - i)) * h2
  rw [e]
  exact P.sub_mem (P.sub_mem (P.add_mem (P.mul_mem_left _ hi) (P.mul_mem_left _ hσi))
    (P.mul_mem_left _ hσi)) (P.mul_mem_right _ hx)

private theorem card_quotient_comap_sq_eq_card_quotient_of_involution (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) :
    Nat.card (A ⧸ P.comap ι) ^ 2 = Nat.card (B ⧸ P) := by
  classical
  haveI := hP
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  have hle : P ≤ P.comap σ := le_of_eq hc.symm
  set sb : B ⧸ P →+* B ⧸ P := Ideal.quotientMap P σ hle with hsb
  set φ : A ⧸ P.comap ι →+* B ⧸ P := Ideal.quotientMap P ι le_rfl with hφ
  have hsbmk : ∀ x, sb (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) :=
    fun x => Ideal.quotientMap_mk
  have hsb2 : ∀ c, sb (sb c) = c := by
    intro c
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hsbmk, hsbmk, hσ]
  have hφmk : ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk P (ι a) :=
    fun a => Ideal.quotientMap_mk
  have hsbφ : ∀ c, sb (φ c) = φ c := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hφmk, hsbmk, (hfix (ι a)).2 ⟨a, rfl⟩]
  have hφinj : Function.Injective φ := Ideal.quotientMap_injective
  have hlift : ∀ c, sb c = c → ∃ a, φ a = c := by
    intro c hcfix
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hsbmk] at hcfix
    have hx : x - σ x ∈ P := Ideal.Quotient.eq.1 hcfix.symm
    obtain ⟨a, ha⟩ := exists_sub_iota_mem_of_sub_involution_mem hσ hfix hP hc hθ x hx
    exact ⟨Ideal.Quotient.mk _ a, by rw [hφmk]; exact (Ideal.Quotient.eq.2 ha).symm⟩
  set th := Ideal.Quotient.mk P θ with hth
  have hδ : th - sb th ≠ 0 := by
    rw [hth, hsbmk, ← map_sub, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hθ

  let f : (A ⧸ P.comap ι) × (A ⧸ P.comap ι) → B ⧸ P := fun p => φ p.1 + φ p.2 * th
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [f] at h
      have h2 := congrArg sb h
      simp only [map_add, map_mul, hsbφ] at h2
      have hb : φ b = φ b' := by
        have h3 : (φ b - φ b') * (th - sb th) = 0 := by linear_combination h - h2
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact sub_eq_zero.1 h4
        · exact absurd h4 hδ
      have ha : φ a = φ a' := by
        rw [hb] at h
        exact add_right_cancel h
      exact Prod.ext (hφinj ha) (hφinj hb)
    · intro y
      set bb := (y - sb y) / (th - sb th) with hbb_def
      have hbb : sb bb = bb := by
        rw [hbb_def, map_div₀, map_sub, map_sub, hsb2, hsb2,
          show sb y - y = -(y - sb y) by ring, show sb th - th = -(th - sb th) by ring,
          neg_div_neg_eq]
      have hmul : bb * (th - sb th) = y - sb y := div_mul_cancel₀ _ hδ
      set aa := y - bb * th with haa_def
      have haa : sb aa = aa := by
        rw [haa_def, map_sub, map_mul, hbb]
        linear_combination hmul
      obtain ⟨a, ha⟩ := hlift aa haa
      obtain ⟨b, hb⟩ := hlift bb hbb
      refine ⟨(a, b), ?_⟩
      simp only [f, ha, hb, haa_def]
      ring
  rw [sq, ← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

theorem exists_sq_card_quot (hσ : ∀ x, σ (σ x) = x) {P : Ideal B} (hP : P.IsMaximal)
    (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) : ∃ q : ℕ, Nat.card (B ⧸ P) = q ^ 2 := by
  classical
  set S : Subring B := RingHom.eqLocus σ (RingHom.id B) with hS
  have hfix' : ∀ x, σ x = x ↔ x ∈ Set.range (S.subtype) := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact a.2
  exact ⟨Nat.card (S ⧸ P.comap S.subtype), (card_quotient_comap_sq_eq_card_quotient_of_involution (ι := S.subtype) hσ hfix' hP hc hθ).symm⟩

theorem card_quot_inert (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) :
    Nat.card (A ⧸ P.comap ι) ^ 2 = Nat.card (B ⧸ P) := by
  exact card_quotient_comap_sq_eq_card_quotient_of_involution hσ hfix hP hc hθ

theorem map_comap_of_inert (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) :
    (P.comap ι).map ι = P := by
  have hσP : ∀ p ∈ P, σ p ∈ P := fun p hp => Ideal.mem_comap.1 (hc.symm ▸ hp)

  have hmem : ∀ z, σ z = z → z ∈ P → z ∈ (P.comap ι).map ι := by
    intro z hz hzP
    obtain ⟨a, rfl⟩ := (hfix z).1 hz
    exact Ideal.mem_map_of_mem ι (Ideal.mem_comap.2 hzP)
  refine le_antisymm Ideal.map_comap_le fun y hy => ?_
  have hσδ : σ (θ - σ θ) = -(θ - σ θ) := by
    rw [map_sub, hσ]
    ring
  have hDP : (θ - σ θ) * (θ - σ θ) ∉ P := fun h => hθ ((hP.isPrime.mem_or_mem h).elim id id)
  obtain ⟨u, i, hi, hui⟩ := hP.exists_inv hDP
  have h2 : σ u * ((θ - σ θ) * (θ - σ θ)) + σ i = 1 := by
    have := congrArg σ hui
    rwa [map_add, map_mul, map_mul, hσδ, map_one, neg_mul_neg] at this
  set v := u * σ u * ((θ - σ θ) * (θ - σ θ)) with hv
  set j := 1 - v * ((θ - σ θ) * (θ - σ θ)) with hj
  have hjfix : σ j = j := by
    rw [hj, hv]
    simp only [map_sub, map_mul, map_one, hσ]
    ring
  have hjP : j ∈ P := by
    have e : j = i + σ i - i * σ i := by
      rw [hj, hv]
      linear_combination (-σ u * ((θ - σ θ) * (θ - σ θ))) * hui + (-(1 - i)) * h2
    rw [e]
    exact P.sub_mem (P.add_mem hi (hσP i hi)) (P.mul_mem_left _ (hσP i hi))
  have hT : ∀ w ∈ P, w + σ w ∈ (P.comap ι).map ι := fun w hw =>
    hmem _ (by rw [map_add, hσ, add_comm]) (P.add_mem hw (hσP w hw))
  have e : y = y * j + ((y * θ + σ (y * θ)) - σ θ * (y + σ y)) * (v * (θ - σ θ)) := by
    rw [hj, map_mul]
    ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hmem j hjfix hjP))
    (Ideal.mul_mem_right _ _ (Ideal.sub_mem _ (hT _ (P.mul_mem_right _ hy))
      (Ideal.mul_mem_left _ _ (hT y hy))))

end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
