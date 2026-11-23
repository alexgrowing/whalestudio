import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quot_pow_maximal_charP_local_card : ∀ (L : Type) [Field L] [NumberField L] (la J : Ideal (𝓞 L)) [la.IsMaximal] (l e b : ℕ), l.Prime → 0 < e → 0 < b → la ⊔ J = ⊤ → Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e * J → CharP (𝓞 L ⧸ la ^ (e * b)) (l ^ b) ∧ Finite (𝓞 L ⧸ la ^ (e * b)) ∧ ∃ π : 𝓞 L ⧸ la ^ (e * b), (∀ x : 𝓞 L ⧸ la ^ (e * b), ¬ IsUnit x ↔ π ∣ x) ∧ Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ (e * b))} = Ideal.span {π ^ e} ∧ Nat.card (𝓞 L ⧸ la ^ (e * b)) = Nat.card ((𝓞 L ⧸ la ^ (e * b)) ⧸ Ideal.span {π}) ^ (b * e) := by
  intro L _ _ la J hmax l e b hl he hb hJ hspan
  have hn0 : e * b ≠ 0 := Nat.mul_ne_zero he.ne' hb.ne'
  set n := e * b with hn
  set q := Ideal.Quotient.mk (la ^ n) with hq
  have hlla : ((l : ℕ) : 𝓞 L) ∈ la := by
    have : ((l:ℕ) : 𝓞 L) ∈ la ^ e * J := by rw [← hspan]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.pow_le_self he.ne' : la ^ e ≤ la) ((Ideal.mul_le_left : la ^ e * J ≤ la ^ e) this)
  have hl0 : ((l : ℕ) : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hla0 : la ≠ ⊥ := fun h => hl0 (by rw [h] at hlla; simpa using hlla)
  have hlatop : la ≠ ⊤ := hmax.ne_top
  have hpowle : ∀ i j : ℕ, la ^ i ≤ la ^ j ↔ j ≤ i := fun i j =>
    ⟨fun h => by
      by_contra hc
      rw [not_le] at hc
      exact absurd h (Ideal.pow_right_strictAnti la hla0 hlatop hc).not_ge,
     fun h => Ideal.pow_le_pow_right h⟩
  have hle : la ^ n ≤ la := Ideal.pow_le_self hn0
  have hnil : ∀ c ∈ la, IsNilpotent (q c) := fun c hc =>
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hc n⟩
  have hunit : ∀ a : 𝓞 L, IsUnit (q a) ↔ a ∉ la := by
    intro a
    constructor
    · intro hu ha
      obtain ⟨d, hd⟩ := hu.exists_right_inv
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective d
      have : a * c - 1 ∈ la ^ n := by
        rw [← Ideal.Quotient.eq]; simpa [hq] using hd
      have h1 : (1 : 𝓞 L) ∈ la := by
        have := la.sub_mem (la.mul_mem_right c ha) (hle this)
        simpa using this
      exact hlatop ((Ideal.eq_top_iff_one _).mpr h1)
    · intro ha
      obtain ⟨c, y, hy, hcy⟩ := hmax.exists_inv ha
      have h1 : q c * q a = 1 - q y := by
        rw [← map_mul, ← map_one q, ← map_sub, ← hcy]; simp
      have : IsUnit (q c * q a) := h1 ▸ (hnil y hy).isUnit_one_sub
      exact isUnit_of_mul_isUnit_right this
  have hmem : ∀ a : 𝓞 L, q a ∈ la.map q ↔ a ∈ la := fun a => Ideal.mem_quotient_iff_mem hle

  obtain ⟨π₀, hπla, hπ2⟩ := SetLike.exists_of_lt ((Ideal.pow_right_strictAnti la hla0 hlatop) (by norm_num : 1 < 2))
  replace hπla : π₀ ∈ la := by simpa using hπla
  change π₀ ∉ la ^ 2 at hπ2
  have hQ : Ideal.span {π₀} ⊔ la ^ 2 = la := by
    have := Ideal.eq_prime_pow_of_succ_lt_of_le (P := la) (I := Ideal.span {π₀} ⊔ la ^ 2) hla0 (i := 1)
      (lt_of_le_of_ne le_sup_right (fun h => hπ2 (h ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π₀))))
      (by rw [pow_one]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hπla) (Ideal.pow_le_self two_ne_zero))
    simpa using this
  have hk : ∀ k, 1 ≤ k → la ≤ Ideal.span {π₀} ⊔ la ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [pow_one]; exact le_sup_right
    | succ k _ ih =>
      calc la = Ideal.span {π₀} ⊔ la ^ 2 := hQ.symm
        _ ≤ Ideal.span {π₀} ⊔ la * (Ideal.span {π₀} ⊔ la ^ k) :=
            sup_le_sup_left (by rw [pow_two]; exact Ideal.mul_mono_right ih) _
        _ = Ideal.span {π₀} ⊔ (la * Ideal.span {π₀} ⊔ la ^ (k + 1)) := by rw [Ideal.mul_sup, pow_succ']
        _ ≤ Ideal.span {π₀} ⊔ la ^ (k + 1) :=
            sup_le le_sup_left (sup_le (le_trans Ideal.mul_le_right le_sup_left) le_sup_right)
  have hm : Ideal.span {q π₀} = la.map q := by
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]; exact (hmem π₀).mpr hπla
    · calc la.map q ≤ (Ideal.span {π₀} ⊔ la ^ n).map q := Ideal.map_mono (hk n (Nat.one_le_iff_ne_zero.mpr hn0))
        _ = Ideal.span {q π₀} := by
            rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hq, Ideal.map_quotient_self, sup_bot_eq]
  have hJtop : J.map q = ⊤ := by
    have : (1 : 𝓞 L) ∈ la ⊔ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp this
    have hz' : q z = 1 - q y := by rw [← map_one q, ← hyz, map_add]; ring
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem q hz) (hz' ▸ (hnil y hy).isUnit_one_sub)
  have hlspan : Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ n)} = (la.map q) ^ e := by
    have : ((l : ℕ) : 𝓞 L ⧸ la ^ n) = q (l : 𝓞 L) := (map_natCast q l).symm
    rw [this, ← Set.image_singleton, ← Ideal.map_span, hspan, Ideal.map_mul, Ideal.map_pow, hJtop, Ideal.mul_top]
  refine ⟨⟨fun k => ?_⟩, ?_, q π₀, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    obtain ⟨v, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0.ne' l hl.ne_one
    have hcop : Nat.Coprime l m' := (Nat.Prime.coprime_iff_not_dvd hl).mpr hm'
    have hm'la : ((m' : ℕ) : 𝓞 L) ∉ la := by
      intro h
      obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      have h1 : ((u * l + w * m' : ℤ) : 𝓞 L) = 1 := by rw [huw]; simp
      push_cast at h1
      have : (1 : 𝓞 L) ∈ la := h1 ▸ la.add_mem (la.mul_mem_left _ hlla) (la.mul_mem_left _ h)
      exact hlatop ((Ideal.eq_top_iff_one _).mpr this)
    have hmu : IsUnit ((m' : ℕ) : 𝓞 L ⧸ la ^ n) := by
      rw [← map_natCast q]; exact (hunit _).mpr hm'la
    rw [Nat.cast_mul, Nat.cast_pow, hmu.mul_left_eq_zero, ← Ideal.span_singleton_eq_bot,
      ← Ideal.span_singleton_pow, hlspan, ← pow_mul, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, hq,
      Ideal.mk_ker, hpowle, (Nat.Coprime.pow_left b hcop).dvd_mul_right,
      Nat.pow_dvd_pow_iff_le_right hl.one_lt, hn]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h he, fun h => Nat.mul_le_mul_left e h⟩
  · exact Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero n hla0)
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← Ideal.mem_span_singleton, hm, hmem]
    exact (not_congr (hunit a)).trans not_not
  · rw [← Ideal.span_singleton_pow, hm, hlspan]
  · have hc1 : Nat.card ((𝓞 L ⧸ la ^ n) ⧸ la.map q) = Nat.card (𝓞 L ⧸ la) :=
      Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv
    have hc2 : ∀ I : Ideal (𝓞 L), Nat.card (𝓞 L ⧸ I) = Ideal.absNorm I := fun I => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hm, hc1, hc2, hc2, map_pow, hn, mul_comm e b]

end GlobalTheory
