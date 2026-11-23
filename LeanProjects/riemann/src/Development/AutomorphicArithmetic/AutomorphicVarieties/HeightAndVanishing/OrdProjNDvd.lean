import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ordProj_N_dvd (h : Host) (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hq : p ∣ h.q) : ordProj[p] h.N ∣ h.q := by
  obtain ⟨hq1, _, hd, _, hcop⟩ := h.pair
  have hq0 : h.q ≠ 0 := h.chi.ne.out
  have hqd : ¬ p ∣ h.q1 * h.d := fun hpd =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpd hcop) hq)
  have hL0 : (2 ^ (h.ex + 2)).lcm h.q ≠ 0 := Nat.lcm_ne_zero (pow_ne_zero _ two_ne_zero) hq0
  have hM0 : h.q1 * h.d ≠ 0 := mul_ne_zero hq1.ne_zero hd.ne_zero
  have hlcm : ((2 ^ (h.ex + 2)).lcm h.q).factorization p = h.q.factorization p := by
    simp [Nat.factorization_lcm (pow_ne_zero _ two_ne_zero) hq0, Nat.factorization_pow,
      Nat.prime_two.factorization, Finsupp.single_apply, Ne.symm h2]
  show p ^ (Nat.factorization ((2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d))) p ∣ h.q
  rw [Nat.factorization_mul hL0 hM0, Finsupp.add_apply, hlcm,
    Nat.factorization_eq_zero_of_not_dvd hqd, add_zero]
  exact Nat.ordProj_dvd _ _

private theorem rem_comp {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (r : ℕ)
    (hr : r.Prime) :
    comp r (χ * (comp r χ)⁻¹) = 1 ∧ (∀ p, p.Prime → p ≠ r → comp p (χ * (comp r χ)⁻¹) = comp p χ) ∧
      orderOf (χ * (comp r χ)⁻¹) ∣ orderOf χ := by
  have hA := compAlg O N r hr
  refine ⟨?_, fun p hp hpr => ?_, ?_⟩
  · rw [hA.2.1, hA.2.2.2.1, (hA.2.2.2.2.2.1 χ).1, mul_inv_cancel]
  · have hB := compAlg O N p hp
    rw [hB.2.1, hB.2.2.2.1, (hB.2.2.2.2.2.1 χ).2.2.2 r hr (Ne.symm hpr), inv_one, mul_one]
  · rw [orderOf_dvd_iff_pow_eq_one, mul_pow, inv_pow, pow_orderOf_eq_one,
      orderOf_dvd_iff_pow_eq_one.mp (hA.2.2.2.2.2.1 χ).2.1, inv_one, mul_one]

theorem UpperTheory.V.HV.hostTh1 :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 →
      comp 2 (th0 l ψ) = psi2 ψ ∧ th0 l ψ = psi2 ψ * th1 l ψ ∧ orderOf (th1 l ψ) ∣ 2 * h.o ∧ ¬ l ∣ orderOf (th1 l ψ) ∧
      Odd (th1 l ψ).conductor ∧ (th1 l ψ ^ 2).conductor ∣ h.q ∧ comp 2 (chiP l ψ) = psi2 ψ ∧ comp l (chiP l ψ) = 1 ∧
      ¬ l ∣ orderOf (chiP l ψ) ∧ (∀ r, r.Prime → r ≠ l → comp r (chiP l ψ) = comp r (th0 l ψ)) ∧
      ∀ r, r.Prime → r ≠ 2 → orderOf (comp r (th0 l ψ)) ∣ 2 * h.o := by
  intro h O _ _ ψ hψ l hl hl2
  have hC := hostComp h O ψ hψ
  have hpos := hC.2.1
  have hPO := partOrd _ l hl ψ hpos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ψ ^ n = th0 l ψ := by
    have hz : lPrime l ψ ∈ Subgroup.zpowers ψ := hPO.2.2.2.2.1
    rw [← (orderOf_pos_iff.mp hpos).mem_powers_iff_mem_zpowers] at hz
    exact (Submonoid.mem_powers_iff _ _).mp hz
  have hcθ : ∀ r, r.Prime → comp r (th0 l ψ) = comp r ψ ^ n := fun r hr => by
    rw [← hn, (compAlg O h.N r hr).2.2.2.2.1]
  have h11 : ∀ r, r.Prime → r ≠ 2 → orderOf (comp r (th0 l ψ)) ∣ 2 * h.o := fun r hr hr2 => by
    rw [hcθ r hr]
    exact (orderOf_pow_dvd n).trans (hC.2.2 r hr hr2).1
  have hκ : comp 2 (kap l ψ) = 1 := by
    obtain ⟨a, ha⟩ := (compOrd O h.N (kap l ψ) 2 Nat.prime_two).2.1
    have hdk : orderOf (comp 2 (kap l ψ)) ∣ l ^ (orderOf ψ).factorization l := by
      rw [← hPO.1]
      exact ((compAlg O h.N 2 Nat.prime_two).2.2.2.2.2.1 (kap l ψ)).2.1
    rw [← orderOf_eq_one_iff, ha]
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero]
    · exfalso
      rw [ha] at hdk
      have h2l := (dvd_pow_self 2 h0.ne').trans hdk
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).1 (Nat.prime_two.dvd_of_dvd_pow h2l)).symm
  have h1 : comp 2 (th0 l ψ) = psi2 ψ := by
    show comp 2 (th0 l ψ) = comp 2 ψ
    conv_rhs => rw [← dirichletPrimeToLPart_mul_lPowerPart l ψ]
    rw [(compAlg O h.N 2 Nat.prime_two).2.1, hκ, mul_one]
  have hR2 := rem_comp (th0 l ψ) 2 Nat.prime_two
  have hRl := rem_comp (th0 l ψ) l hl
  have hth1 : th1 l ψ = th0 l ψ * (comp 2 (th0 l ψ))⁻¹ := rfl
  have hchi : chiP l ψ = th0 l ψ * (comp l (th0 l ψ))⁻¹ := rfl
  have hc2 : comp 2 (th1 l ψ) = 1 := by
    rw [hth1]
    exact hR2.1
  have hcp : ∀ p, p.Prime → p ≠ 2 → comp p (th1 l ψ) = comp p (th0 l ψ) := fun p hp hp2 => by
    rw [hth1]
    exact hR2.2.1 p hp hp2
  have hnlθ : ¬ l ∣ orderOf (th0 l ψ) := hPO.2.2.1
  have hNpf : ∀ p ∈ h.N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  refine ⟨h1, ?_, ?_, fun hd => hnlθ (hd.trans (by rw [hth1]; exact hR2.2.2)), ?_, ?_, ?_, ?_,
    fun hd => hnlθ (hd.trans (by rw [hchi]; exact hRl.2.2)), fun r hr hrl => ?_, h11⟩
  · rw [hth1, h1, mul_comm, inv_mul_cancel_right]
  · apply orderOf_dvd_of_pow_eq_one
    apply (compAlg O h.N 2 Nat.prime_two).2.2.2.2.2.2.2
    intro p hp
    by_cases hp2 : p = 2
    · subst hp2
      rw [hc2, one_pow]
    · rw [hcp p (hNpf p hp) hp2]
      exact orderOf_dvd_iff_pow_eq_one.mp (h11 p (hNpf p hp) hp2)
  · rw [hth1, (compCond O h.N (th0 l ψ) 2 Nat.prime_two).2.2.1]
    exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (th0 l ψ).conductor_ne_zero)
  · rw [(compCond O h.N (th1 l ψ ^ 2) 2 Nat.prime_two).2.2.2.2.2 h.q h.q_dvd]
    intro p hp
    have hpp := hNpf p hp
    by_cases hp2 : p = 2
    · subst hp2
      rw [(compAlg O h.N 2 Nat.prime_two).2.2.2.2.1, hc2, one_pow, DirichletCharacter.conductor_one]
      exact one_dvd _
    · by_cases hpq : p ∣ h.q
      · rw [(compCond O h.N (th1 l ψ ^ 2) p hpp).1]
        refine dvd_trans ?_ (ordProj_N_dvd h p hpp hp2 hpq)
        apply Nat.pow_dvd_pow
        exact (Nat.factorization_le_iff_dvd (th1 l ψ ^ 2).conductor_ne_zero (NeZero.ne h.N)).mpr
          (DirichletCharacter.conductor_dvd_level _) p
      · rw [(compAlg O h.N p hpp).2.2.2.2.1, hcp p hpp hp2, hcθ p hpp, ← pow_mul, mul_comm n 2, pow_mul,
          (hC.2.2 p hpp hp2).2.2.1 hpq, one_pow, DirichletCharacter.conductor_one]
        exact one_dvd _
  · rw [hchi, hRl.2.1 2 Nat.prime_two (Ne.symm hl2), h1]
  · rw [hchi]
    exact hRl.1
  · rw [hchi]
    exact hRl.2.1 r hr hrl
