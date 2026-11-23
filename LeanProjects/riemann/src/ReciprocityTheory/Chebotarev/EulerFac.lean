import ReciprocityTheory.Chebotarev.NZIdeal

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

def Smooth {E : Type} [Field E] [NumberField E] (S : Finset (Prm E)) (a : Ideal (𝓞 E)) : Prop :=
  ∀ q : Prm E, q.asIdeal ∣ a → q ∈ S

theorem prm_eq_of_dvd {E : Type} [Field E] [NumberField E] {p q : Prm E}
    (h : p.asIdeal ∣ q.asIdeal) : p = q :=
  IsDedekindDomain.HeightOneSpectrum.ext ((prime_dvd_prime_iff_eq p.prime q.prime).1 h)

theorem smooth_empty_iff {E : Type} [Field E] [NumberField E] {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) :
    Smooth ∅ a ↔ a = ⊤ := by
  constructor
  · intro hs
    by_contra htop
    obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal a htop
    have hMb : M ≠ ⊥ := fun h => ha (le_bot_iff.1 (h ▸ haM))
    let q : Prm E := ⟨M, hM.isPrime, hMb⟩
    exact absurd (hs q (Ideal.dvd_iff_le.2 haM)) (Finset.notMem_empty q)
  · rintro rfl q hq
    rw [← Ideal.one_eq_top] at hq
    exact absurd (isUnit_of_dvd_one hq) q.prime.not_isUnit

theorem smooth_insert_mul {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} {b : Ideal (𝓞 E)}
    (q : Prm E) (k : ℕ) (hb : Smooth S b) : Smooth (insert q S) (q.asIdeal ^ k * b) := by
  intro p hp
  rcases p.prime.dvd_or_dvd hp with h | h
  · exact Finset.mem_insert.2 (Or.inl (prm_eq_of_dvd (p.prime.dvd_of_dvd_pow h)))
  · exact Finset.mem_insert_of_mem (hb p h)

theorem smooth_insert_decomp {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} (q : Prm E)
    {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) (hs : Smooth (insert q S) a) :
    ∃ (k : ℕ) (b : Ideal (𝓞 E)), b ≠ ⊥ ∧ Smooth S b ∧ a = q.asIdeal ^ k * b := by
  obtain ⟨k, b, hqb, hab⟩ := WfDvdMonoid.max_power_factor (a₀ := a) ha q.irreducible
  refine ⟨k, b, ?_, ?_, hab⟩
  · rintro rfl
    exact ha (by rw [hab, Ideal.mul_bot])
  · intro p hp
    have hpa : p.asIdeal ∣ a := hab ▸ dvd_mul_of_dvd_right hp _
    rcases Finset.mem_insert.1 (hs p hpa) with h | h
    · exact absurd (h ▸ hp) hqb
    · exact h

theorem smooth_mul_inj {E : Type} [Field E] [NumberField E] {S : Finset (Prm E)} {q : Prm E} (hq : q ∉ S)
    {b b' : Ideal (𝓞 E)} (hb : Smooth S b) (hb' : Smooth S b') {k k' : ℕ}
    (h : q.asIdeal ^ k * b = q.asIdeal ^ k' * b') : k = k' ∧ b = b' := by
  have hq0 : q.asIdeal ≠ 0 := q.ne_bot
  have key : ∀ {c c' : Ideal (𝓞 E)} {m m' : ℕ}, Smooth S c → m < m' →
      q.asIdeal ^ m * c ≠ q.asIdeal ^ m' * c' := by
    intro c c' m m' hc hlt he
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [show q.asIdeal ^ (m + n + 1) * c' = q.asIdeal ^ m * (q.asIdeal ^ (n + 1) * c') by
      rw [← mul_assoc, ← pow_add, add_assoc]] at he
    have hc' := mul_left_cancel₀ (pow_ne_zero m hq0) he
    exact hq (hc q (hc' ▸ dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero n)) _))
  rcases lt_trichotomy k k' with hlt | rfl | hlt
  · exact absurd h (key hb hlt)
  · exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k hq0) h⟩
  · exact absurd h.symm (key hb' hlt)

end ReciprocityTheory.Cheb
