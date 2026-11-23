import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {M : ℕ} (N : ℕ) [NeZero N] (hN : N ∣ M)
    (s : G ℚ Ω) (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.cls ℚ Ω N s = 1 := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 s 1 (fun ζ hζ => ?_)
  obtain ⟨k, rfl⟩ := hN
  rw [h ζ (by rw [pow_mul, hζ, one_pow]), Units.val_one, ZMod.val_one_eq_one_mod]
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hN1 : N = 1 := by
      have := NeZero.pos N
      omega
    subst hN1
    simpa using hζ

private theorem dirG_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {M N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) (hN : N ∣ M) (s : G ℚ Ω) (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.dirG ℚ Ω χ s = 1 := by
  rw [Chr.dirG, MonoidHom.comp_apply, cls_one N hN s h, map_one]

private theorem dirG_pow_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {a m : ℕ} (h : χ ^ a = 1) (ha : a ∣ m) : Chr.dirG ℚ Ω χ ^ m = 1 := by
  obtain ⟨k, rfl⟩ := ha
  refine MonoidHom.ext fun g => Units.ext ?_
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one,
    Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rw [pow_mul, ← MulChar.pow_apply_coe, h, MulChar.one_apply_coe, one_pow]

private theorem tot_two (k : ℕ) : Nat.totient (2 ^ k) ∣ 2 ^ k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.totient_prime_pow_succ Nat.prime_two, pow_succ]
    exact Nat.mul_dvd_mul_left _ (by norm_num)

private theorem pow_tot {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient N = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
    ZMod.pow_totient, Units.val_one, map_one]

private theorem pow_tot_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient χ.conductor = 1 := by
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  rw [show χ ^ Nat.totient χ.conductor = DirichletCharacter.changeLevel χ.conductor_dvd_level
      (χ.primitiveCharacter ^ Nat.totient χ.conductor) by
    rw [map_pow, χ.changeLevel_primitiveCharacter]]
  rw [pow_tot, map_one]

theorem UpperTheory.V.GradeZeroInterpolatingElement.levOf :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → ∀ n' p₁ m₀ : ℕ, Aut.OfChar D e ψ n' p₁ m₀ → c2 ψ ≤ n' → m₀ ∣ h.o → (Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.ψ ∧ Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.ξ ∧ Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.om) ∧ D.ψ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 ∧ D.ξ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 ∧ D.om ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 := by
  intro Ω _ _ _ h t _ l _ c e _ _ _ ψ hψ D hD n' p₁ m₀ hc hc2 hm₀
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hp₁, ξ', ξ₀, -, -, hord, hξ⟩ := hc.xi
  have hpsi := hc.psi
  have hMN : h.N ∣ l * 2 ^ n' * h.N * p₁ := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hMp : p₁ ∣ l * 2 ^ n' * h.N * p₁ := dvd_mul_left _ _
  have hM2 : 2 ^ n' ∣ l * 2 ^ n' * h.N * p₁ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  have hMl : l ∣ l * 2 ^ n' * h.N * p₁ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hEo : h.o ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hE2o : 2 * h.o ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_left _ _
  have hE2 : 2 ^ n' ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hEl : l - 1 ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hIs : IsOmT c D.om := ⟨hD.om_pow, fun σ => Ideal.Quotient.eq.mp (hD.om_bar σ)⟩
  have hker := ((omT Ω l c).2 D.om hIs).2.1
  have htot2 : Nat.totient (2 ^ n') ∣ (l - 1) * 2 ^ n' * (2 * h.o) := (tot_two n').trans hE2
  have hpsiE : ψ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 := by
    have hchar := ((Host.mem_X h).1 hψ).1
    have hcomp := hostComp h c.O ψ hchar
    refine (compAlg c.O h.N 2 Nat.prime_two).2.2.2.2.2.2.2 ψ _ (fun p hp => ?_)
    have pp := Nat.prime_of_mem_primeFactors hp
    by_cases hp2 : p = 2
    · subst hp2
      have hcond := (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1
      have h1 := pow_tot_cond (psi2 ψ)
      rw [← hcond] at h1
      have hdv : Nat.totient (2 ^ c2 ψ) ∣ (l - 1) * 2 ^ n' * (2 * h.o) :=
        ((tot_two _).trans (Nat.pow_dvd_pow 2 hc2)).trans hE2
      obtain ⟨k, hk⟩ := hdv
      rw [hk, pow_mul]
      unfold psi2 at h1
      rw [h1, one_pow]
    · exact orderOf_dvd_iff_pow_eq_one.mp (((hcomp.2.2 p pp hp2).1).trans hE2o)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro s hs
    rw [hpsi]
    exact dirG_one ψ hMN s hs
  · intro s hs
    rw [hξ, MonoidHom.mul_apply, dirG_one ξ₀ hMp s hs, dirG_one ξ' hM2 s hs, mul_one]
  · intro s hs
    have h1 : Chr.cls ℚ Ω l s = 1 := cls_one l hMl s hs
    have h2 : s ∈ D.om.ker := by
      rw [hker]
      exact h1
    exact h2
  · rw [hpsi]
    exact dirG_pow_one ψ hpsiE dvd_rfl
  · rw [hξ, mul_pow, dirG_pow_one ξ₀ (pow_orderOf_eq_one ξ₀) (by rw [hord]; exact hm₀.trans hEo),
      dirG_pow_one ξ' (pow_tot ξ') htot2, mul_one]
  · obtain ⟨k, hk⟩ := hEl
    rw [hk, pow_mul, hD.om_pow, one_pow]
