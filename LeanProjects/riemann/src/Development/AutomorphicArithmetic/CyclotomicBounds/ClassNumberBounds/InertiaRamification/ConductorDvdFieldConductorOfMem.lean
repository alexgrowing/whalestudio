import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ExistsHostDataWild
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HostDegree

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps : DirichletCharacter ℂ N}
  {Y : Subgroup (DirichletCharacter ℂ N)}

private theorem natCard_sup_mul_natCard_inf {G : Type*} [CommGroup G] (H K : Subgroup G) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) K (H ⊔ K) bot_le le_sup_right
  have h2 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ H) H bot_le inf_le_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h1 h2
  rw [Subgroup.relIndex_sup_right] at h1
  rw [Subgroup.inf_relIndex_right, inf_comm] at h2
  rw [← h1, ← h2]
  ring

private theorem mem_closure_pair_of_order_two {G : Type*} [CommGroup G] {a b x : G} (ha : a ^ 2 = 1)
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

private theorem conductor_dvd_fieldConductor_of_mem {ψ : DirichletCharacter ℂ N} (hψ : ψ ∈ Y) :
    ψ.conductor ∣ fieldCond Y :=
  (mem_condDvd_iff _ ψ).1.1 (((fieldCond_sup Y ⊥ 1).2.2 _).1 dvd_rfl hψ)

private theorem fieldConductor_dvd_level : fieldCond Y ∣ N :=
  ((fieldCond_sup Y ⊥ 1).2.2 _).2 fun ψ _ => (mem_condDvd_iff _ ψ).1.2 ψ.conductor_dvd_level

private theorem fieldConductor_ne_zero_of_level : fieldCond Y ≠ 0 :=
  ne_zero_of_dvd_ne_zero (NeZero.ne N) fieldConductor_dvd_level

private theorem exists_char_prime_dvd_conductor {p : ℕ} (hp : p.Prime) (h : p ∣ fieldCond Y) :
    ∃ ψ ∈ Y, p ∣ ψ.conductor := by
  have h1 : fieldCond Y ∣
      ∏ ψ ∈ (Set.toFinite (Y : Set (DirichletCharacter ℂ N))).toFinset, ψ.conductor :=
    Finset.lcm_dvd fun ψ hψ => Finset.dvd_prod_of_mem _ hψ
  obtain ⟨ψ, hψ, h2⟩ := hp.prime.exists_mem_finset_dvd (h.trans h1)
  exact ⟨ψ, by simpa using hψ, h2⟩

private theorem host_primes_not_dvd_conductor (h : HostDataOf n d q₁ ch ps Y) :
    d ≠ q₁ ∧ ¬ d ∣ Nat.lcm (4 * n) (fieldCond Y) ∧ ¬ q₁ ∣ Nat.lcm (4 * n) (fieldCond Y) := by
  obtain ⟨⟨e, he, rfl⟩, -, hd, hd16, hq, hq8, -, -, hY⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have key : ∀ p : ℕ, p.Prime → p % 2 = 1 → (∀ ψ ∈ Y, ¬ p ∣ ψ.conductor) →
      ¬ p ∣ Nat.lcm (4 * 2 ^ e) (fieldCond Y) := by
    intro p hp hp2 hpχ hdiv
    rcases (hp.dvd_mul).1 (hdiv.trans (Nat.lcm_dvd_mul _ _)) with h1 | h1
    · rw [h4] at h1
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
      omega
    · obtain ⟨ψ, hψ, h2⟩ := exists_char_prime_dvd_conductor hp h1
      exact hpχ ψ hψ h2
  exact ⟨by omega, key d hd (by omega) fun ψ hψ => (hY ψ hψ).1,
    key q₁ hq (by omega) fun ψ hψ => (hY ψ hψ).2⟩

private theorem fieldConductor_real_cyclotomic_sup (h : HostDataOf n d q₁ ch ps Y) :
    fieldCond (realCycSup n Y) = Nat.lcm (4 * n) (fieldCond Y) := by
  obtain ⟨⟨e, he, rfl⟩, hN, -⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  rw [realCycSup, (fieldCond_sup _ _ 1).1]
  rw [h4] at hN ⊢
  rw [(fieldCond_evenPart_condDvd_two_pow hN (by omega)).1]

private theorem card_character_pair_disjoint_real (h : HostDataOf n d q₁ ch ps Y) :
    Nat.card (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N))) = 4 ∧
      Disjoint (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)))
        (realCycSup n Y) := by
  obtain ⟨hne, hdL, hqL⟩ := host_primes_not_dvd_conductor h
  have hrest := fieldConductor_real_cyclotomic_sup h
  obtain ⟨-, -, hd, -, hq, -, ⟨hch2, -, hchc⟩, ⟨hps2, -, hpsc⟩, -⟩ := h
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
      simp only [SetLike.mem_coe, mem_closure_pair_of_order_two hch2 hps2, Set.mem_insert_iff,
        Set.mem_singleton_iff]
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_eq_four]
    refine ⟨1, ch, ps, ch * ps, hch1.symm, hps1.symm, hcp1.symm, hcp, ?_, ?_, rfl⟩
    · intro h1
      exact hps1 (left_eq_mul.1 h1)
    · intro h1
      exact hch1 (right_eq_mul.1 h1)
  · rw [Subgroup.disjoint_def]
    intro x hx hx'
    have hle := ((fieldCond_sup (realCycSup n Y) ⊥ 1).2.2
      (Nat.lcm (4 * n) (fieldCond Y))).1 (by rw [hrest])
    have hxc := (mem_condDvd_iff _ x).1.1 (hle hx')
    rcases (mem_closure_pair_of_order_two hch2 hps2).1 hx with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd (hchc ▸ hxc) hdL
    · exact absurd (hpsc ▸ hxc) hqL
    · exact absurd (hprod.trans hxc) hdL

theorem HostDataOf.card (h : HostDataOf n d q₁ ch ps Y) :
    Disjoint (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N))) (realCycSup n Y) ∧
      ∃ s o : ℕ, Nat.card ↥(evenPart (condDvd N (4 * n)) ⊓ Y) = 2 ^ s ∧
        s ≤ (fieldCond Y).factorization 2 - 2 ∧ Nat.card Y = 2 ^ s * o ∧
        (evenPart (condDvd N (4 * n))).relIndex (realCycSup n Y) = o ∧
        Nat.card (realCycSup n Y) = n * o ∧
        Nat.card (hostCharsOf n ch ps Y) = 4 * n * o ∧
        Nat.card (evenPart (hostCharsOf n ch ps Y)) = 2 * n * o ∧
        8 ∣ Nat.card (evenPart (hostCharsOf n ch ps Y)) ∧
        o ≤ Nat.card Y ∧ Nat.card Y ≤ Nat.totient (fieldCond Y) := by
  obtain ⟨hA, hdisj⟩ := card_character_pair_disjoint_real h
  refine ⟨hdisj, ?_⟩
  obtain ⟨⟨e, he, rfl⟩, hN, -, -, -, -, ⟨-, hodd, -⟩, -⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have hB : Nat.card (evenPart (condDvd N (4 * 2 ^ e))) = 2 ^ e := by
    rw [h4] at hN ⊢
    rw [card_evenPart_condDvd_two_pow hN, Nat.add_sub_cancel]
  have haN : 2 ^ (fieldCond Y).factorization 2 ∣ N :=
    (Nat.ordProj_dvd _ 2).trans fieldConductor_dvd_level
  have hle : evenPart (condDvd N (4 * 2 ^ e)) ⊓ Y ≤
      evenPart (condDvd N (2 ^ (fieldCond Y).factorization 2)) := by
    rintro ψ ⟨h1, h2⟩
    obtain ⟨h3, h5⟩ := ((card_evenPart _).1 ψ).1 h1
    refine ((card_evenPart _).1 ψ).2 ⟨(mem_condDvd_iff _ ψ).1.2 ?_, h5⟩
    have h6 := (mem_condDvd_iff _ ψ).1.1 h3
    rw [h4] at h6
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h6
    have h7 : ψ.conductor ∣ fieldCond Y := conductor_dvd_fieldConductor_of_mem h2
    rw [hj] at h7 ⊢
    exact pow_dvd_pow 2
      ((Nat.prime_two.pow_dvd_iff_le_factorization fieldConductor_ne_zero_of_level).1 h7)
  have hdv := Subgroup.card_dvd_of_le hle
  rw [card_evenPart_condDvd_two_pow haN] at hdv
  obtain ⟨s, hs, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdv
  have hdv2 := Subgroup.card_dvd_of_le
    (inf_le_right : evenPart (condDvd N (4 * 2 ^ e)) ⊓ Y ≤ _)
  rw [hcard] at hdv2
  obtain ⟨o, ho⟩ := hdv2
  have hC : Nat.card ↥(realCycSup (2 ^ e) Y) = 2 ^ e * o := by
    have h1 := natCard_sup_mul_natCard_inf (evenPart (condDvd N (4 * 2 ^ e))) Y
    rw [hcard, hB, ho] at h1
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ s by positivity)
    rw [realCycSup, h1]
    ring
  have hR : (evenPart (condDvd N (4 * 2 ^ e))).relIndex (realCycSup (2 ^ e) Y) = o := by
    have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (DirichletCharacter ℂ N))
      (evenPart (condDvd N (4 * 2 ^ e))) (realCycSup (2 ^ e) Y) bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hB, hC] at h1
    exact Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ e by positivity) h1
  have hH : Nat.card (hostCharsOf (2 ^ e) ch ps Y) = 4 * 2 ^ e * o := by
    have h1 := natCard_sup_mul_natCard_inf (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)))
      (realCycSup (2 ^ e) Y)
    rw [hdisj.eq_bot, Subgroup.card_bot, mul_one, hA, hC, ← mul_assoc] at h1
    exact h1
  have hmem : ch ∈ hostCharsOf (2 ^ e) ch ps Y :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hE : Nat.card (evenPart (hostCharsOf (2 ^ e) ch ps Y)) = 2 * 2 ^ e * o := by
    have h1 := (card_evenPart _).2 ⟨ch, hmem, hodd⟩
    rw [hH] at h1
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [← h1]
    ring
  refine ⟨s, o, hcard, hs, ho, hR, hC, hH, hE, ?_, ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le he
    rw [hE]
    exact ⟨2 ^ f * o, by ring⟩
  · rw [ho]
    exact Nat.le_mul_of_pos_left o (by positivity)
  · rw [← (mem_condDvd_iff (fieldCond Y) (1 : DirichletCharacter ℂ N)).2
      fieldConductor_dvd_level]
    exact Subgroup.card_le_of_le (((fieldCond_sup Y ⊥ 1).2.2 _).1 dvd_rfl)

end KStar.Ram
