import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.RedOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowLtSqMulOfPrimitiveCharPowEqOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem not_over_odd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (h2 : A.valuation ((2 : ℕ) : Ω) < 1) {n : ℕ}
    (hn : Odd n) : ¬ A.valuation (n : Ω) < 1 := by
  intro h
  obtain ⟨k, rfl⟩ := hn
  have h1 : A.valuation (((2 : ℕ) : Ω) * (k : Ω)) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le h2 ((A.valuation_le_one_iff _).2 (natCast_mem A k))
  have h3 := A.valuation.map_sub_lt h h1
  have e : ((2 * k + 1 : ℕ) : Ω) - ((2 : ℕ) : Ω) * (k : Ω) = 1 := by push_cast; ring
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

private theorem all_mem_range (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ∈ (proj 2 (2 ^ n)).range := by
  rw [(projFacts (2 ^ n) 2 Nat.prime_two).2.2.2.2.2.1, MonoidHom.mem_ker]
  have e : ordCompl[2] (2 ^ n) = 1 := by
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same, Nat.div_self (by positivity)]
  have : Subsingleton (ZMod (ordCompl[2] (2 ^ n))) := by rw [e]; infer_instance
  exact Subsingleton.elim _ _

private theorem tot_dvd (k : ℕ) : Nat.totient (2 ^ k) ∣ 2 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two hk]
    simpa using pow_dvd_pow 2 (Nat.sub_le k 1)

private theorem pow_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {k : ℕ}
    (h : χ.conductor = 2 ^ k) : χ ^ 2 ^ k = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one,
      MulChar.one_apply_coe]
  have h2 : Nat.totient χ.conductor ∣ 2 ^ k := by
    rw [h]
    exact tot_dvd k
  obtain ⟨j, hj⟩ := h2
  rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]

theorem UpperTheory.V.Ws.exists_inertia_element_at_two_xi_pow_four_ne_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 → ∃ g ∈ Ine (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1 := by
  rintro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, -, -, -, -, -, -, hψ, -, hp, ξ', ξ₀, hprim, -, -, hξ⟩ κ j hκ A hA0
  have hA : A.valuation ((2 : ℕ) : Ω) < 1 := by rwa [Nat.cast_ofNat]
  have hlp : l.Prime := hl.out
  have hlo : Odd l := hlp.odd_of_ne_two hG.l_odd
  have hom : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hG.om_bar σ⟩
  have h1 : Ine (F := ℚ) A ≤ D.om.ker := ((omT Ω l c).2 D.om hom).2.2.2.2.2.1 _ (not_over_odd _ hA hlo)
  have hq : 0 < h.q := NeZero.pos _
  have ho : 0 < h.o := orderOf_pos _
  obtain ⟨-, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
  have b3 : 2 ^ (c2 ψ + 6) ≤ 2 ^ h.nII l ψ := le_trans (by
      rw [mul_assoc, mul_assoc]
      exact Nat.le_mul_of_pos_right _ (by have := hlp.pos; positivity)) b2
  have p1 := pow_cond (psi2 ψ) (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
  clear b2
  generalize h.nII l ψ = n at *
  generalize c2 ψ = k at *
  have h3 : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨u, hu, hc⟩ : ZMod.unitOfCoprime 3 h3 ∈ (Ine (F := ℚ) A).map (Chr.cls ℚ Ω (2 ^ n)) := by
    rw [(compIne Ω (2 ^ n) 2 Nat.prime_two _ hA).1]
    exact all_mem_range _ _
  have hξu : D.ξ u = ξ'.toUnitHom (ZMod.unitOfCoprime 3 h3) := by
    have h4 : Chr.cls ℚ Ω 1 u = 1 := Subsingleton.elim _ _
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, h4, hc, map_one, one_mul]
  have hψu : D.ψ u ^ 2 ^ k = 1 := by
    rw [hψ, ((compIne Ω h.N 2 Nat.prime_two _ hA).2 c.O ψ).1 u hu, Chr.dirG, MonoidHom.comp_apply]
    ext1
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe]
    change (psi2 ψ ^ 2 ^ k) _ = _
    rw [p1, MulChar.one_apply_coe, Units.val_one]
  have hg : u ^ (2 ^ k * l ^ j) ∈ Ine (F := ℚ) A := pow_mem hu _
  refine ⟨u ^ (2 ^ k * l ^ j), hg, ?_, ?_, fun hb => ?_⟩
  · have a1 := hG.om_bar (u ^ (2 ^ k * l ^ j))
    have a2 : D.om (u ^ (2 ^ k * l ^ j)) = 1 := h1 hg
    have a3 : D.ψ (u ^ (2 ^ k * l ^ j)) = 1 := by rw [map_pow, pow_mul, hψu, one_pow]
    simp only [Raw.bar] at a1 ⊢
    rw [a2, Units.val_one, map_one] at a1
    rw [Raw.Psi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, a3, mul_one, Units.val_pow_eq_pow_val,
      map_pow (residue c.O), ← a1, one_pow]
  · rw [map_pow, mul_comm, pow_mul, ← MonoidHom.pow_apply κ (l ^ j), hκ, MonoidHom.one_apply, one_pow]
  · have a1 : D.ξ u ^ (2 ^ (k + 2) * l ^ j) = 1 := by
      refine large₂.redOne c (2 ^ n) (Nat.Coprime.pow_right _ ((Nat.coprime_primes hlp Nat.prime_two).2 hG.l_odd)) _ ?_ ?_
      · obtain ⟨m, hm⟩ := tot_dvd n
        have a2 : D.ξ u ^ 2 ^ n = 1 := by
          rw [hξu, ← map_pow]
          have : ZMod.unitOfCoprime 3 h3 ^ (Nat.totient (2 ^ n) * m) = 1 := by
            rw [pow_mul, ZMod.pow_totient, one_pow]
          rw [← hm] at this
          rw [this, map_one]
        rw [← pow_mul, mul_comm, pow_mul, a2, one_pow]
      · simp only [Raw.bar] at hb
        rw [← hb, ← map_pow (residue c.O), ← Units.val_pow_eq_pow_val, map_pow D.ξ, ← pow_mul]
        congr 3
        ring
    have a2 := congrArg Units.val a1
    rw [Units.val_pow_eq_pow_val, hξu, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime, Units.val_one] at a2
    have a3 := UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ' hprim 3 (k + 2) (l ^ j) (by decide) (by norm_num) hlo.pow a2
    have a4 : 2 ^ (k + 6) = 16 * 2 ^ (k + 2) := by ring
    omega
