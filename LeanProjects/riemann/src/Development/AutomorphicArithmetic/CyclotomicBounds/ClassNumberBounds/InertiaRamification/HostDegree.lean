import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.TwoPower
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.QuadraticCharacterLegendreSymbol

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps χ : DirichletCharacter ℂ N}

private theorem hostDegree_card_sup {G : Type*} [CommGroup G] (H K : Subgroup G) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) K (H ⊔ K) bot_le le_sup_right
  have h2 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ H) H bot_le inf_le_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h1 h2
  rw [Subgroup.relIndex_sup_right] at h1
  rw [Subgroup.inf_relIndex_right, inf_comm] at h2
  rw [← h1, ← h2]
  ring

private theorem hostDegree_mem_pair {G : Type*} [CommGroup G] {a b x : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) :
    x ∈ Subgroup.closure ({a, b} : Set G) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hA : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hB : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  constructor
  · intro hx
    obtain ⟨i, j, rfl⟩ := Subgroup.mem_closure_pair.1 hx
    have key : ∀ (c : G), c ^ 2 = 1 → ∀ i : ℤ, c ^ i = 1 ∨ c ^ i = c := by
      intro c hc i
      have hc' : c ^ (2 : ℤ) = 1 := by exact_mod_cast hc
      rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
      · left; rw [zpow_mul, hc', one_zpow]
      · right; rw [zpow_add, zpow_mul, hc', one_zpow, one_mul, zpow_one]
    rcases key a ha i with h1 | h1 <;> rcases key b hb j with h2 | h2 <;> simp [h1, h2]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact hA
    · exact hB
    · exact mul_mem hA hB

omit [NeZero N] in
private theorem hostDegree_arith (h : HostData n d q₁ ch ps χ) :
    d ≠ q₁ ∧ ¬ d ∣ Nat.lcm (4 * n) χ.conductor ∧ ¬ q₁ ∣ Nat.lcm (4 * n) χ.conductor := by
  obtain ⟨⟨e, he, rfl⟩, -, hd, hd16, hq, hq8, -, -, hdχ, hqχ⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have key : ∀ p : ℕ, p.Prime → p % 2 = 1 → ¬ p ∣ χ.conductor →
      ¬ p ∣ Nat.lcm (4 * 2 ^ e) χ.conductor := by
    intro p hp hp2 hpχ hdiv
    rcases (hp.dvd_mul).1 (hdiv.trans (Nat.lcm_dvd_mul _ _)) with h1 | h1
    · rw [h4] at h1
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
      omega
    · exact hpχ h1
  exact ⟨by omega, key d hd (by omega) hdχ, key q₁ hq (by omega) hqχ⟩

private theorem hostDegree_fieldCond_rest (h : HostData n d q₁ ch ps χ) :
    fieldCond (evenPart (condDvd N (4 * n)) ⊔ Subgroup.zpowers χ) =
      Nat.lcm (4 * n) χ.conductor := by
  obtain ⟨⟨e, he, rfl⟩, hN, -⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  rw [(fieldCond_sup _ _ χ).1, (fieldCond_sup ⊥ ⊥ χ).2.1]
  rw [h4] at hN ⊢
  rw [(fieldCond_evenPart_condDvd_two_pow hN (by omega)).1]

theorem HostData.disjoint (h : HostData n d q₁ ch ps χ) :
    Nat.card (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N))) = 4 ∧
      Disjoint (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)))
        (evenPart (condDvd N (4 * n)) ⊔ Subgroup.zpowers χ) := by
  obtain ⟨hne, hdL, hqL⟩ := hostDegree_arith h
  have hrest := hostDegree_fieldCond_rest h
  obtain ⟨-, -, hd, -, hq, -, ⟨hch2, -, hchc⟩, ⟨hps2, -, hpsc⟩, -, -⟩ := h
  have hprod : d ∣ (ch * ps).conductor := by
    have h1 : ch * ps * ps = ch := by rw [mul_assoc, ← sq, hps2, mul_one]
    have h2 := conductor_mul_dvd_lcm_conductor (ch * ps) ps
    rw [h1, hchc, hpsc] at h2
    rcases (hd.dvd_mul).1 (h2.trans (Nat.lcm_dvd_mul _ _)) with h3 | h3
    · exact h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hd hq).1 h3) hne
  have hch1 : ch ≠ 1 := by
    intro h1
    rw [h1, conductor_one] at hchc
    exact hd.one_lt.ne hchc
  have hps1 : ps ≠ 1 := by
    intro h1
    rw [h1, conductor_one] at hpsc
    exact hq.one_lt.ne hpsc
  have hcp : ch ≠ ps := by
    intro h1
    rw [h1, hpsc] at hchc
    exact hne hchc.symm
  have hcp1 : ch * ps ≠ 1 := by
    intro h1
    rw [h1, conductor_one] at hprod
    exact hd.one_lt.ne' (Nat.dvd_one.1 hprod)
  constructor
  · have hset : ((Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)) :
        Subgroup (DirichletCharacter ℂ N)) : Set (DirichletCharacter ℂ N)) =
        {1, ch, ps, ch * ps} := by
      ext x
      simp only [SetLike.mem_coe, hostDegree_mem_pair hch2 hps2, Set.mem_insert_iff,
        Set.mem_singleton_iff]
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_eq_four]
    refine ⟨1, ch, ps, ch * ps, hch1.symm, hps1.symm, hcp1.symm, hcp, ?_, ?_, rfl⟩
    · intro h1
      exact hps1 (left_eq_mul.1 h1)
    · intro h1
      exact hch1 (right_eq_mul.1 h1)
  · rw [Subgroup.disjoint_def]
    intro x hx hx'
    have hle := ((fieldCond_sup (evenPart (condDvd N (4 * n)) ⊔ Subgroup.zpowers χ) ⊥ χ).2.2
      (Nat.lcm (4 * n) χ.conductor)).1 (by rw [hrest])
    have hxc := (mem_condDvd_iff _ x).1.1 (hle hx')
    rcases (hostDegree_mem_pair hch2 hps2).1 hx with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd (hchc ▸ hxc) hdL
    · exact absurd (hpsc ▸ hxc) hqL
    · exact absurd (hprod.trans hxc) hdL

theorem HostData.card (h : HostData n d q₁ ch ps χ) :
    ∃ s o : ℕ, Nat.card ↥(evenPart (condDvd N (4 * n)) ⊓ Subgroup.zpowers χ) = 2 ^ s ∧
      s ≤ condExp 2 χ - 2 ∧ orderOf χ = 2 ^ s * o ∧
      Nat.card (hostChars n ch ps χ) = 4 * n * o ∧
      Nat.card (evenPart (hostChars n ch ps χ)) = 2 * n * o ∧
      8 ∣ Nat.card (evenPart (hostChars n ch ps χ)) := by
  obtain ⟨hA, hdisj⟩ := h.disjoint
  obtain ⟨⟨e, he, rfl⟩, hN, -, -, -, -, ⟨-, hodd, -⟩, -⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have hB : Nat.card (evenPart (condDvd N (4 * 2 ^ e))) = 2 ^ e := by
    rw [h4] at hN ⊢
    rw [card_evenPart_condDvd_two_pow hN, Nat.add_sub_cancel]
  have haN : 2 ^ condExp 2 χ ∣ N := (Nat.ordProj_dvd _ 2).trans χ.conductor_dvd_level
  have hle : evenPart (condDvd N (4 * 2 ^ e)) ⊓ Subgroup.zpowers χ ≤
      evenPart (condDvd N (2 ^ condExp 2 χ)) := by
    rintro ψ ⟨h1, ⟨k, h2⟩⟩
    obtain ⟨h3, h5⟩ := ((card_evenPart _).1 ψ).1 h1
    refine ((card_evenPart _).1 ψ).2 ⟨(mem_condDvd_iff _ ψ).1.2 ?_, h5⟩
    have h6 := (mem_condDvd_iff _ ψ).1.1 h3
    rw [h4] at h6
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h6
    have h7 : ψ.conductor ∣ χ.conductor := by
      rw [← h2]
      exact conductor_zpow_dvd χ k
    rw [hj] at h7 ⊢
    exact pow_dvd_pow 2
      ((Nat.prime_two.pow_dvd_iff_le_factorization χ.conductor_ne_zero).1 h7)
  have hdv := Subgroup.card_dvd_of_le hle
  rw [card_evenPart_condDvd_two_pow haN] at hdv
  obtain ⟨s, hs, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdv
  have hdv2 := Subgroup.card_dvd_of_le
    (inf_le_right : evenPart (condDvd N (4 * 2 ^ e)) ⊓ Subgroup.zpowers χ ≤ _)
  rw [hcard, Nat.card_zpowers] at hdv2
  obtain ⟨o, ho⟩ := hdv2
  have hC : Nat.card ↥(evenPart (condDvd N (4 * 2 ^ e)) ⊔ Subgroup.zpowers χ) = 2 ^ e * o := by
    have h1 := hostDegree_card_sup (evenPart (condDvd N (4 * 2 ^ e))) (Subgroup.zpowers χ)
    rw [hcard, hB, Nat.card_zpowers, ho] at h1
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ s by positivity)
    rw [h1]
    ring
  have hH : Nat.card (hostChars (2 ^ e) ch ps χ) = 4 * 2 ^ e * o := by
    have h1 := hostDegree_card_sup (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)))
      (evenPart (condDvd N (4 * 2 ^ e)) ⊔ Subgroup.zpowers χ)
    rw [hdisj.eq_bot, Subgroup.card_bot, mul_one, hA, hC, ← mul_assoc] at h1
    exact h1
  have hmem : ch ∈ hostChars (2 ^ e) ch ps χ :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hE : Nat.card (evenPart (hostChars (2 ^ e) ch ps χ)) = 2 * 2 ^ e * o := by
    have h1 := (card_evenPart _).2 ⟨ch, hmem, hodd⟩
    rw [hH] at h1
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [← h1]
    ring
  refine ⟨s, o, hcard, hs, ho, hH, hE, ?_⟩
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [hE]
  exact ⟨2 ^ f * o, by ring⟩

end KStar.Ram
