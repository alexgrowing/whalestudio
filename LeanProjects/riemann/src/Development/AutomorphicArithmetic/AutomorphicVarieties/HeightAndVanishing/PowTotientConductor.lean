import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CmDatumCharTwoAdicOrderBounds
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem pow_totient_conductor {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient χ.conductor = 1 := by
  obtain ⟨hd, χ₀, e⟩ := χ.factorsThrough_conductor
  have h0 : χ₀ ^ Nat.totient χ.conductor = 1 := by
    refine MulChar.ext (fun a => ?_)
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
      ZMod.pow_totient, Units.val_one, map_one]
  have h1 : DirichletCharacter.changeLevel hd χ₀ ^ Nat.totient χ.conductor = 1 := by
    rw [← map_pow, h0, map_one]
  rwa [← e] at h1

private theorem totient_two_pow_dvd (c : ℕ) : Nat.totient (2 ^ c) ∣ 2 ^ c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two hc]
    simpa using Nat.pow_dvd_pow 2 (Nat.sub_le c 1)

theorem UpperTheory.V.HV.vsOrd :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 → 2 ^ c2 ψ < h.R1 l ψ →
      orderOf ψ ≤ 2 * h.o * (16 * h.o * (l * h.q) ^ 2 * l ^ (2 * Nat.totient (4 * h.o))) := by
  intro h O _ _ ψ hψ l hl hl2 hlt
  obtain ⟨-, -, -, hR1, -⟩ := cmDatum_char_two_adic_order_bounds h O ψ hψ l hl hl2
  obtain ⟨-, -, -, hopos, -⟩ := hostIndex h
  have hc2 : comp 2 ψ ^ (2 ^ c2 ψ) = 1 := by
    obtain ⟨-, -, -, hpow2, -⟩ := compCond O h.N ψ 2 Nat.prime_two
    have ht := pow_totient_conductor (comp 2 ψ)
    rw [show (comp 2 ψ).conductor = 2 ^ c2 ψ from hpow2.symm] at ht
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one ht).trans (totient_two_pow_dvd _))
  have hall : ψ ^ (2 * h.o * 2 ^ c2 ψ) = 1 := by
    apply (compAlg O h.N 2 Nat.prime_two).2.2.2.2.2.2.2 ψ
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases h2p : p = 2
    · subst h2p
      rw [mul_comm, pow_mul, hc2, one_pow]
    · have hd := ((hostComp h O ψ hψ).2.2 p hpp h2p).1
      rw [pow_mul, orderOf_dvd_iff_pow_eq_one.mp hd, one_pow]
  have hmpos : 0 < 2 * h.o * 2 ^ c2 ψ := by positivity
  calc orderOf ψ ≤ 2 * h.o * 2 ^ c2 ψ := Nat.le_of_dvd hmpos (orderOf_dvd_of_pow_eq_one hall)
    _ ≤ _ := Nat.mul_le_mul_left _ (hlt.le.trans hR1)
