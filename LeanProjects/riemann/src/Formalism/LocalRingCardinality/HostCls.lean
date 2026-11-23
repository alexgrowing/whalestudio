import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

open NumberField Formalism.FrobeniusOrbits Formalism.HC

namespace Formalism.BasicNotions

section cls

variable {φ : Frame} (H : HostRaw φ) {p : ℕ}

theorem primeClass_eq_ramified_iff : primeClass H p = .ram2 ↔ p ∈ H.small := by
  unfold primeClass
  split_ifs <;> simp_all

private theorem ne_q_and_ne_d_of_mem_small (hp : p ∈ H.small) : p ≠ H.q ∧ p ≠ H.d := by
  rw [HostRaw.small, Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hdvd, -⟩ := hp
  have hc := H.QS_coprime
  constructor
  · intro heq
    rw [heq] at hdvd hpp
    have h1 : H.q ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdvd (dvd_mul_right _ _)
    rw [hc.gcd_eq_one] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
  · intro heq
    rw [heq] at hdvd hpp
    have h1 : H.d ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdvd (dvd_mul_left _ _)
    rw [hc.gcd_eq_one] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem primeClass_eq_ramQ_iff : primeClass H p = .ramQ ↔ p = H.q := by
  have hs : p ∈ H.small → p ≠ H.q := fun h => (ne_q_and_ne_d_of_mem_small H h).1
  unfold primeClass
  split_ifs <;> simp_all

private theorem q_ne_d' : H.q ≠ H.d := by
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨-, -, h1, h2, -⟩ := hh
  omega

theorem primeClass_eq_ramD_iff : primeClass H p = .ramD ↔ p = H.d := by
  have hs : p ∈ H.small → p ≠ H.d := fun h => (ne_q_and_ne_d_of_mem_small H h).2
  have hqd := q_ne_d' H
  unfold primeClass
  split_ifs <;> simp_all

theorem primeClass_eq_splitK_iff : primeClass H p = .splitK ↔
    p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧ jacobiSym (-(H.d : ℤ)) p = 1 := by
  unfold primeClass
  split_ifs <;> simp_all

theorem primeClass_eq_signal_iff : primeClass H p = .signal ↔
    p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧ jacobiSym (-(H.d : ℤ)) p ≠ 1 ∧ H.psAt p = 1 := by
  unfold primeClass
  split_ifs <;> simp_all

theorem primeClass_eq_inert_iff : primeClass H p = .inertClass ↔
    p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧ jacobiSym (-(H.d : ℤ)) p ≠ 1 ∧ H.psAt p ≠ 1 := by
  unfold primeClass
  split_ifs <;> simp_all

theorem primeClass_two : primeClass H 2 = .ram2 := by
  apply (primeClass_eq_ramified_iff H).2
  rw [HostRaw.small, Nat.mem_primeFactors]
  exact ⟨Nat.prime_two, dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd, H.QS_pos.ne'⟩
theorem primeClass_q : primeClass H H.q = .ramQ := (primeClass_eq_ramQ_iff H).2 rfl
theorem primeClass_d : primeClass H H.d = .ramD := (primeClass_eq_ramD_iff H).2 rfl

theorem dvd_condN_iff_primeClass (hp : p.Prime) : p ∣ H.condN ↔
    primeClass H p = .ram2 ∨ primeClass H p = .ramQ ∨ primeClass H p = .ramD := by
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨hq, hd, -, -, -⟩ := hh
  have hQS := H.QS_pos.ne'
  show p ∣ H.QS * H.q * H.d ↔ _
  rw [primeClass_eq_ramified_iff, primeClass_eq_ramQ_iff, primeClass_eq_ramD_iff, hp.dvd_mul, hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp hq, Nat.prime_dvd_prime_iff_eq hp hd, HostRaw.small, Nat.mem_primeFactors]
  tauto

theorem not_dvd_condN_iff_primeClass (hp : p.Prime) : ¬ p ∣ H.condN ↔
    primeClass H p = .splitK ∨ primeClass H p = .signal ∨ primeClass H p = .inertClass := by
  rw [dvd_condN_iff_primeClass H hp]
  unfold primeClass
  split_ifs <;> simp

variable {H}

theorem not_dvd_of_splitK (hp : p.Prime) (h : primeClass H p = .splitK) : ¬ p ∣ H.condN := (not_dvd_condN_iff_primeClass H hp).2 (Or.inl h)

theorem not_dvd_of_signal (hp : p.Prime) (h : primeClass H p = .signal) : ¬ p ∣ H.condN := (not_dvd_condN_iff_primeClass H hp).2 (Or.inr (Or.inl h))

theorem not_dvd_conductor_of_inert (hp : p.Prime) (h : primeClass H p = .inertClass) : ¬ p ∣ H.condN := (not_dvd_condN_iff_primeClass H hp).2 (Or.inr (Or.inr h))

theorem jacobi_d_eq_one_or (hp : p.Prime) (hd : p ≠ H.d) :
    jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1 := by
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨-, hdp, -, -, -⟩ := hh
  apply jacobiSym.eq_one_or_neg_one
  show Nat.gcd (-(H.d : ℤ)).natAbs (p : ℤ).natAbs = 1
  simpa using (Nat.coprime_primes hdp hp).2 (Ne.symm hd)

private theorem not_dvd_condN_iff' (hp : p.Prime) :
    ¬ p ∣ H.condN ↔ p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d := by
  rw [dvd_condN_iff_primeClass H hp, primeClass_eq_ramified_iff, primeClass_eq_ramQ_iff,
    primeClass_eq_ramD_iff]
  tauto

theorem primeClass_eq_splitK_iff' (hp : p.Prime) : primeClass H p = .splitK ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = 1 := by
  rw [primeClass_eq_splitK_iff, not_dvd_condN_iff' hp]
  tauto

theorem primeClass_eq_signal_iff' (hp : p.Prime) : primeClass H p = .signal ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = 1 := by
  rw [primeClass_eq_signal_iff, not_dvd_condN_iff' hp]
  have key : p ≠ H.d → (jacobiSym (-(H.d : ℤ)) p ≠ 1 ↔ jacobiSym (-(H.d : ℤ)) p = -1) := fun hd => by
    rcases jacobi_d_eq_one_or hp hd with h | h <;> simp [h]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3⟩, (key h3).1 h4, h5⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, h2, h3, (key h3).2 h4, h5⟩

private theorem psAt_eq_one_or_neg_one (hp : p.Prime) (h : ¬ p ∣ H.condN) :
    H.psAt p = 1 ∨ H.psAt p = -1 := by
  have hc : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hp).2 h
  unfold HostRaw.psAt
  rw [dif_pos hc]
  rcases Int.units_eq_one_or ((H.art (ZMod.unitOfCoprime p hc)).1.1) with h1 | h1 <;> simp [h1]

theorem primeClass_eq_inert_iff_symbols (hp : p.Prime) : primeClass H p = .inertClass ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = -1 := by
  rw [primeClass_eq_inert_iff, not_dvd_condN_iff' hp]
  have key : p ≠ H.d → (jacobiSym (-(H.d : ℤ)) p ≠ 1 ↔ jacobiSym (-(H.d : ℤ)) p = -1) := fun hd => by
    rcases jacobi_d_eq_one_or hp hd with h | h <;> simp [h]
  have key2 : p ∉ H.small → p ≠ H.q → p ≠ H.d → (H.psAt p ≠ 1 ↔ H.psAt p = -1) := fun h1 h2 h3 => by
    rcases psAt_eq_one_or_neg_one (H := H) hp ((not_dvd_condN_iff' (H := H) hp).2 ⟨h1, h2, h3⟩) with h | h <;> simp [h]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3⟩, (key h3).1 h4, (key2 h1 h2 h3).1 h5⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, h2, h3, (key h3).2 h4, (key2 h1 h2 h3).2 h5⟩

end cls

namespace Ranks

variable (R : Ranks)

theorem n_eq_ord : R.n = R.ord := rfl
theorem f_eq_ord : R.f = 2 * R.ord := rfl
theorem n_pos' : 0 < R.n := by
  show 0 < R.ord
  have h1 := R.m_le_f
  have h2 := R.two_le_m
  omega
theorem two_pow_le_n : 2 ^ R.e ≤ R.n := Nat.le_of_dvd R.n_pos' R.toFrame.two_pow_dvd_ord
theorem baseRank_le_rank : R.n0 ≤ R.n := R.toFrame.cyclic_order_le_exponent

end Ranks

namespace Host

variable {R : Ranks} (H : Host R)

include H in
theorem four_le_two_pow : 4 ≤ 2 ^ R.e := by
  have h := H.two_le_e
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ R.e := Nat.pow_le_pow_right (by norm_num) h

include H in
theorem four_le_n' : 4 ≤ R.n := le_trans (four_le_two_pow H) R.two_pow_le_n

include H in
theorem psAt_prime {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ H.condN) : H.psAt p = jacobiSym (-(H.q : ℤ)) p := by
  have hc : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hp).2 h
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨hq, -, hq8, -, -⟩ := hh
  have hq4 : H.q % 4 = 3 := by omega
  have h2 : p ≠ 2 := by
    intro h2
    apply h
    rw [h2]
    have h5 : 2 ∣ H.QS := dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h5 _) _
  have hpo : Odd p := hp.odd_of_ne_two h2
  have hqo : Odd H.q := hq.odd_of_ne_two (by omega)
  have step1 : H.psAt p = jacobiSym (p : ℤ) H.q := by
    unfold HostRaw.psAt
    rw [dif_pos hc, H.flPS (ZMod.unitOfCoprime p hc)]
    apply jacobiSym.mod_left'
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Int.natCast_mod]
    apply Int.emod_emod_of_dvd
    exact Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp hpo
    omega
  rw [step1, jacobiSym.neg _ hpo]
  rcases h4 with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hqo]
  · rw [ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four h3 hq4]
    ring

private theorem sum_even_of_prod_neg_one_zpow_eq_one {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι]
    (k : ι → ℤ) (h : ∏ τ, (-1 : K) ^ k τ = 1) : ∃ z : ℤ, ∑ τ, k τ = 2 * z := by
  have key : ∀ τ, (-1 : K) ^ k τ = (((-1 : Kˣ) ^ k τ : Kˣ) : K) := fun τ => by
    rw [Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one]
  have hsum : ∀ s : Finset ι, ∏ τ ∈ s, (-1 : Kˣ) ^ k τ = (-1 : Kˣ) ^ (∑ τ ∈ s, k τ) := by
    classical
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  rw [Finset.prod_congr rfl (fun τ _ => key τ), ← Units.coe_prod, hsum] at h
  rcases Int.even_or_odd (∑ τ, k τ) with ⟨w, hw⟩ | hodd
  · exact ⟨w, by rw [hw]; ring⟩
  · exfalso
    rw [hodd.neg_one_zpow, Units.val_neg, Units.val_one] at h
    have h4 : (2 : K) = 0 := by linear_combination -h
    norm_num at h4

variable {H} in

theorem MuCond.even_im_hermitian_sub {ι : Type} [Fintype ι] {g : ι → R.GG} {e : ι → ℚ} (h : H.MuCond g e) (he : ∀ τ, ∃ z : ℤ, e τ = z) :
    ∃ z : ℤ, ∑ τ, e τ = 2 * z := by
  have h1 := h (-1) ⟨2, by norm_num, by norm_num⟩
  simp only [map_neg, map_one] at h1
  obtain ⟨w, hw⟩ := sum_even_of_prod_neg_one_zpow_eq_one (fun τ => (e τ).num) h1
  refine ⟨w, ?_⟩
  have hnum : ∀ τ, (((e τ).num : ℤ) : ℚ) = e τ := fun τ => by
    obtain ⟨z, hz⟩ := he τ
    rw [hz]
    simp
  have h3 : ((∑ τ, (e τ).num : ℤ) : ℚ) = ((2 * w : ℤ) : ℚ) := by exact_mod_cast hw
  push_cast at h3
  simp only [hnum] at h3
  exact h3

theorem finrank_E' : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.der.finrank_E]
  show 4 * R.ord = 2 * (2 * R.ord)
  ring

end Host

end Formalism.BasicNotions
