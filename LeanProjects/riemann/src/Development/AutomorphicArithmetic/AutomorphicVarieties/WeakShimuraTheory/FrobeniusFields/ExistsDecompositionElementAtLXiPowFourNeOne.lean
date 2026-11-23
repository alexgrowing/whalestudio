import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Th1Facts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrdProjNDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowLtSqMulOfPrimitiveCharPowEqOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem dirG_pow {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (k : ℕ) (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (χ ^ k) g = Chr.dirG ℚ Ω χ g ^ k := Units.ext (MulChar.pow_apply_coe χ k _)

private theorem dirG_one {O : Type} [CommRing O] {N : ℕ} [NeZero N] (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (1 : DirichletCharacter O N) g = 1 := Units.ext (MulChar.one_apply_coe _)

private theorem dirG_frob {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ}
    (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ N) {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) :
    (Chr.dirG ℚ Ω χ σ : O) = χ v := by
  have h1 := (ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h
    ((ML.placeBasic Ω).2.2.2.1 A v N ((Nat.Prime.coprime_iff_not_dvd hv).2 hN) hA)
  have h2 := (Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v ((Nat.Prime.coprime_iff_not_dvd hv).2 hN)) fun ζ hζ => by
    rw [h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]
  rw [Chr.dirG, MonoidHom.comp_apply, h2, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

private theorem pow_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {k : ℕ}
    (h : χ.conductor = 2 ^ k) : χ ^ 2 ^ k = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one,
      MulChar.one_apply_coe]
  have h2 : Nat.totient χ.conductor ∣ 2 ^ k := by
    rw [h]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk]
      simpa using pow_dvd_pow 2 (Nat.sub_le k 1)
  obtain ⟨j, hj⟩ := h2
  rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]

private theorem psi_exp (h : Host) {O : Type} [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N) (hψ : h.IsChar ψ)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) :
    ∃ a u : ℕ, Odd u ∧ ψ ^ (2 ^ a * u) = 1 ∧ l ^ 2 * 2 ^ (a + 2) ≤ 2 ^ h.nII l ψ := by
  have hq : 0 < h.q := NeZero.pos _
  have ho : 0 < h.o := orderOf_pos _
  obtain ⟨tψ, ⟨s, hs⟩, -⟩ := X.th1Facts O h.N ψ l hl hl2
  obtain ⟨-, -, t3, -⟩ := hostTh1 h O ψ hψ l hl hl2
  obtain ⟨-, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
  refine ⟨c2 ψ + 1 + h.o.factorization 2, ordCompl[2] h.o * l ^ s, ?_, ?_, ?_⟩
  · exact (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two ho.ne'))).mul (hl.odd_of_ne_two hl2).pow
  · have e1 : 2 ^ (c2 ψ + 1 + h.o.factorization 2) * (ordCompl[2] h.o * l ^ s) = 2 ^ c2 ψ * (2 * h.o) * l ^ s := by
      conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self h.o 2]
      ring
    have p1 := pow_cond (psi2 ψ) (compCond O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
    have p2 := orderOf_dvd_iff_pow_eq_one.1 t3
    rw [e1]
    generalize c2 ψ = k at p1 ⊢
    have p3 : (psi2 ψ * th1 l ψ * kap l ψ) ^ (2 ^ k * (2 * h.o) * l ^ s) = 1 := by
      rw [mul_pow, mul_pow, mul_assoc (2 ^ k), pow_mul, p1, one_pow, one_mul, mul_left_comm, pow_mul, p2, one_pow, one_mul,
        ← mul_assoc, mul_comm, pow_mul, hs, one_pow]
    rwa [← tψ] at p3
  · have v2 : 2 ^ h.o.factorization 2 ≤ h.o := Nat.ordProj_le 2 ho.ne'
    refine le_trans ?_ b2
    calc l ^ 2 * 2 ^ (c2 ψ + 1 + h.o.factorization 2 + 2) = 2 ^ (c2 ψ + 3) * 2 ^ h.o.factorization 2 * l ^ 2 * 1 := by ring
      _ ≤ 2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2 := by
        gcongr
        · norm_num
        · omega
        · exact hl.one_le
        · omega
        · exact Nat.one_le_pow _ _ hq

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.exists_decomposition_element_at_l_xi_pow_four_ne_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1 := by
  intro Ω _ _ _ l hl c D ⟨hD, h, t, e, ψ, _, _, _, hmem, _, hO⟩ κ j hκ A hA
  have hlp : l.Prime := hl.out
  have hl2 := hD.l_odd
  obtain ⟨a, u, hu, hψ, hb⟩ := psi_exp h ψ (h.mem_X.1 hmem).1 hlp hl2
  obtain ⟨_, ξ, ξ₀, hξ, -, h0, dξ⟩ := hO.xi
  rw [orderOf_eq_one_iff] at h0
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  have hfr := hD.sg_frob l hT
  obtain ⟨w, hw, -⟩ := (Chr.placesQ Ω).2.2 l _ A hlp (hD.pl_over l hlp) hA
  have conj : ∀ (γ : G ℚ Ω →* c.Oˣ) (x : G ℚ Ω) (k : ℕ), γ (w⁻¹ * x ^ k * w) = γ x ^ k := fun γ x k => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul, map_pow]
  generalize h.nII l ψ = n at hb ξ hξ dξ
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : 0 < l ^ 2 * 2 ^ a := by have := hlp.pos; positivity
      rw [pow_add, ← mul_assoc] at hb
      omega
    · exact hn
  have h2 : ¬ l ∣ 2 := fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 hd)
  refine ⟨_, hw _ (pow_mem hfr.1 (2 ^ a * u * l ^ j)), ?_, ?_, fun hx => ?_⟩
  · have : D.Psi (D.sg l) = Chr.dirG ℚ Ω ψ (D.sg l) := by
      rw [Raw.Psi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, chiO, MonoidHom.comp_apply, hD.sg_cyc,
        map_one, one_pow, one_mul, hO.psi]
    rw [Raw.bar, conj, this, pow_mul, ← dirG_pow, hψ, dirG_one, one_pow, Units.val_one, map_one]
  · rw [conj, mul_comm, pow_mul, ← MonoidHom.pow_apply, hκ, MonoidHom.one_apply, one_pow]
  · have e1 : 2 ^ a * u * l ^ j * 4 = 2 ^ (a + 2) * (u * l ^ j) := by ring
    rw [Raw.bar, conj, ← map_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, e1, dξ, MonoidHom.mul_apply, h0, dirG_one,
      one_mul] at hx
    have r4 : Chr.dirG ℚ Ω ξ (D.sg l) ^ (2 ^ (a + 2) * (u * l ^ j)) = 1 := by
      refine (congrFacts Ω l c).2.2.2.1 _ _ (Nat.totient (2 ^ n)) ?_ ?_ (one_pow _)
        (Ideal.Quotient.eq.1 (hx.trans (map_one (residue c.O)).symm))
      · rw [Nat.totient_prime_pow Nat.prime_two hn]
        exact fun hd => h2 (hlp.dvd_of_dvd_pow (by simpa using hd))
      · rw [← pow_mul, mul_comm, pow_mul, Chr.dirG, MonoidHom.comp_apply, ← map_pow, ZMod.pow_totient, map_one, one_pow]
    have r5 := congrArg Units.val r4
    rw [Units.val_pow_eq_pow_val, dirG_frob ξ hlp (hD.pl_over l hlp) (fun hd => h2 (hlp.dvd_of_dvd_pow hd)) hfr] at r5
    exact (UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ hξ l (a + 2) _ (hlp.odd_of_ne_two hl2) hlp.one_lt
      (hu.mul (hlp.odd_of_ne_two hl2).pow) r5).not_ge hb
