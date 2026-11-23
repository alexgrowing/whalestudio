import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem kap_pow {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (hψ : 0 < orderOf ψ)
    (l : ℕ) (hl : l.Prime) : ∃ s, kap l ψ ^ l ^ s = 1 := by
  refine ⟨(orderOf ψ).factorization l, ?_⟩
  rw [← (partOrd _ l hl ψ hψ).1]
  exact pow_orderOf_eq_one _

private theorem comp_kap_iff {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N)
    (hψ : 0 < orderOf ψ) (l : ℕ) (hl : l.Prime) (p : ℕ) (hp : p.Prime) :
    comp p (kap l ψ) = 1 ↔ ¬ l ∣ orderOf (comp p ψ) := by
  obtain ⟨h1, -, h3, -⟩ := partOrd _ l hl ψ hψ
  obtain ⟨-, hmul, -, -, -, hsub, -⟩ := compAlg O N p hp
  have hsplit : comp p ψ = comp p (th0 l ψ) * comp p (kap l ψ) := by
    rw [← hmul, dirichletPrimeToLPart_mul_lPowerPart]
  have ha : ¬ l ∣ orderOf (comp p (th0 l ψ)) := fun hd => h3 (hd.trans (hsub _).2.1)
  have hb : orderOf (comp p (kap l ψ)) ∣ l ^ (orderOf ψ).factorization l := by
    rw [← h1]; exact (hsub _).2.1
  have hcop : (orderOf (comp p (th0 l ψ))).Coprime (orderOf (comp p (kap l ψ))) := by
    refine Nat.Coprime.coprime_dvd_right hb ?_
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 ha).symm
  rw [hsplit, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hl.dvd_mul]
  simp only [ha, false_or]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hl).1 hb
  constructor
  · intro h1' hd
    rw [h1', orderOf_one] at hd
    exact hl.ne_one (Nat.dvd_one.1 hd)
  · intro hd
    rw [← orderOf_eq_one_iff, hi]
    rcases i with _ | i
    · exact pow_zero l
    · exfalso
      apply hd
      rw [hi]
      exact dvd_pow_self l (Nat.succ_ne_zero i)

private theorem ordProj_N (h : Host) (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hq : p ∣ h.q) :
    h.N.factorization p = h.q.factorization p := by
  obtain ⟨hq1, -, hd, -, hcop⟩ := h.pair
  have hq0 : h.q ≠ 0 := h.chi.ne.out
  have hqd0 : h.q1 * h.d ≠ 0 := mul_ne_zero hq1.ne_zero hd.ne_zero
  have h20 : (2 : ℕ) ^ (h.ex + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hl0 : (2 ^ (h.ex + 2)).lcm h.q ≠ 0 := Nat.lcm_ne_zero h20 hq0
  have hnd : ¬ p ∣ h.q1 * h.d := fun hd' =>
    hp.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd' hcop) hq)
  have h2nd : ¬ p ∣ 2 ^ (h.ex + 2) := fun h' =>
    h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))
  show ((2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d)).factorization p = _
  rw [Nat.factorization_mul hl0 hqd0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd,
    add_zero, Nat.factorization_lcm h20 hq0, Finsupp.sup_apply, Nat.factorization_eq_zero_of_not_dvd h2nd]
  simp

theorem UpperTheory.V.HV.hostSb :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 →
      (∀ p ∈ Sb l ψ, p.Prime ∧ p ≠ 2 ∧ p ≠ l ∧ p ∣ h.q ∧ p ≡ 1 [MOD l]) ∧ (kap l ψ).conductor ∣ h.q ∧ comp 2 (kap l ψ) = 1 ∧
      (∀ p, p.Prime → p ≠ l → (p ∈ Sb l ψ ↔ l ∣ orderOf (comp p ψ))) ∧ ∀ v ∈ Tb l ψ, v ∣ l * h.q := by
  intro h O _ _ ψ hc l hl hl2
  haveI : NeZero h.N := ⟨h.N_pos.ne'⟩
  obtain ⟨-, hψ, hcomp⟩ := hostComp h O ψ hc
  obtain ⟨s, hs⟩ := kap_pow ψ hψ l hl
  have hlodd : ¬ l ∣ 2 := fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 hd)
  have hc2 : comp 2 (kap l ψ) = 1 := by
    obtain ⟨-, ⟨k, hk⟩, -⟩ := compOrd O h.N (kap l ψ) 2 Nat.prime_two
    obtain ⟨-, -, -, -, -, hsub, -⟩ := compAlg O h.N 2 Nat.prime_two
    have hdv : orderOf (comp 2 (kap l ψ)) ∣ l ^ s :=
      ((hsub _).2.1).trans (orderOf_dvd_of_pow_eq_one hs)
    rw [← orderOf_eq_one_iff, hk]
    rcases k with _ | k
    · exact pow_zero 2
    · exfalso
      rw [hk] at hdv
      have h2 : 2 ∣ l := Nat.prime_two.dvd_of_dvd_pow ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdv)
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).1 h2).symm
  have key : ∀ p, p.Prime → comp p (kap l ψ) ≠ 1 → p ≠ 2 ∧ p ∣ h.q := by
    intro p hp hne
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hne hc2
    refine ⟨hp2, ?_⟩
    by_contra hq
    obtain ⟨-, -, hsq, -⟩ := hcomp p hp hp2
    have h2 : orderOf (comp p ψ) ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq hq)
    exact hne ((comp_kap_iff ψ hψ l hl p hp).2 (fun hd => hlodd (hd.trans h2)))
  have hSb : ∀ p, p ∈ Sb l ψ ↔ p.Prime ∧ p ∣ h.N ∧ p ≠ l ∧ comp p (kap l ψ) ≠ 1 := by
    intro p
    simp only [Sb, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hd, -⟩, h1, h2⟩
      exact ⟨hp, hd, h1, h2⟩
    · rintro ⟨hp, hd, h1, h2⟩
      exact ⟨⟨hp, hd, h.N_pos.ne'⟩, h1, h2⟩
  refine ⟨?_, ?_, hc2, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpp, -, hpl, hne⟩ := (hSb p).1 hp
    obtain ⟨hp2, hpq⟩ := key p hpp hne
    exact ⟨hpp, hp2, hpl, hpq, ((compOrd O h.N (kap l ψ) p hpp).2.2.2 l s hl (Ne.symm hpl) hs hne).1⟩
  · obtain ⟨-, -, -, -, -, hall⟩ := compCond O h.N (kap l ψ) 2 Nat.prime_two
    rw [hall h.q h.q_dvd]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    obtain ⟨hcd, hiff, -⟩ := compCond O h.N (kap l ψ) p hpp
    rw [hcd]
    by_cases hne : comp p (kap l ψ) = 1
    · rw [Nat.factorization_eq_zero_of_not_dvd (hiff.1 hne), pow_zero]
      exact one_dvd _
    · obtain ⟨hp2, hpq⟩ := key p hpp hne
      have hcl := DirichletCharacter.conductor_dvd_level (kap l ψ)
      have hc0 : (kap l ψ).conductor ≠ 0 := fun h0 => h.N_pos.ne' (Nat.eq_zero_of_zero_dvd (h0 ▸ hcl))
      have hle : (kap l ψ).conductor.factorization p ≤ h.q.factorization p := by
        rw [← ordProj_N h p hpp hp2 hpq]
        exact (Nat.factorization_le_iff_dvd hc0 h.N_pos.ne').2 hcl p
      exact (pow_dvd_pow p hle).trans (Nat.ordProj_dvd h.q p)
  · intro p hp hpl
    rw [hSb p]
    constructor
    · rintro ⟨-, -, -, hne⟩
      by_contra hd
      exact hne ((comp_kap_iff ψ hψ l hl p hp).2 hd)
    · intro hd
      refine ⟨hp, ?_, hpl, fun h1 => (comp_kap_iff ψ hψ l hl p hp).1 h1 hd⟩
      by_contra hN
      obtain ⟨-, -, -, -, -, hsub, -⟩ := compAlg O h.N p hp
      rw [(hsub ψ).2.2.1 hN, orderOf_one] at hd
      exact hl.ne_one (Nat.dvd_one.1 hd)
  · intro v hv
    simp only [Tb, Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact dvd_mul_right _ _
    · obtain ⟨hvp, -, -, hne⟩ := (hSb v).1 hv
      exact dvd_mul_of_dvd_right (key v hvp hne).2 _
