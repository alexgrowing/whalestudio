import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem pow_cyc_char_iff_toZModPow_eq {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] [∀ i, HasEnoughRootsOfUnity Ω (l ^ i)]
    (g : Ω ≃+* Ω) (k : ℕ) (c : ZMod (l ^ k)) :
    (∀ t : Ω, t ^ (l ^ k) = 1 → g t = t ^ c.val) ↔
      PadicInt.toZModPow k ((cyclotomicCharacter Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = c := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
    have h1 := cyclotomicCharacter.spec l g ζ hζ.pow_eq_one
    rw [h ζ hζ.pow_eq_one] at h1
    have h2 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
    exact (ZMod.val_injective _ h2).symm
  · rintro h t ht
    rw [cyclotomicCharacter.spec l g t ht, h]

private theorem pow_mod_eq_pow_of_pow_eq_one {Ω : Type} [Field Ω] (t : Ω) (n a : ℕ) (ht : t ^ n = 1) :
    t ^ (a % n) = t ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, ht, one_pow, mul_one]

theorem UpperTheory.V.Odd.fixLev :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (N m : ℕ) [NeZero N], fixMu E Ω (l ^ m) = Un E Ω l m ∧ Uinf E Ω l ⊓ fixMu E Ω N ≤ fixMu E Ω (N * l ^ m) ∧ ∀ (M : ℕ) [NeZero M] (b : (ZMod M)ˣ) (σ : Ω ≃+* Ω), l ^ m ∣ M → CycLift M b σ → (l : ℤ_[l]) ^ m ∣ ((cyclotomicCharacter Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) - (((b : ZMod M).val : ℕ) : ℤ_[l]) := by
  intro E Ω _ _ _ _ _ l _ N m _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  have key : ∀ (g : G E Ω) (k : ℕ),
      PadicInt.toZModPow k ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = 1 ↔
        ∀ t : Ω, t ^ (l ^ k) = 1 → g t = t := by
    intro g k
    rw [← pow_cyc_char_iff_toZModPow_eq l _ k 1]
    refine forall_congr' fun t => imp_congr_right fun ht => ?_
    rw [ZMod.val_one_eq_one_mod, pow_mod_eq_pow_of_pow_eq_one t _ 1 ht, pow_one]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · ext g
    simp only [Un, levU, Subgroup.mem_inf, Subgroup.mem_top, true_and, Subgroup.mem_comap, KStar.TotallyRealRoots.princ,
      cycZ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow, MonoidHom.comp_apply, Units.ext_iff, Units.coe_map,
      MonoidHom.coe_coe, Units.val_one]
    change _ ↔ PadicInt.toZModPow m _ = 1
    rw [key]
    rfl
  · intro g hg
    rcases Subgroup.mem_inf.1 hg with ⟨h1, h2⟩
    have hχ : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) = 1 := by
      simpa only [Uinf, cycU, Subgroup.mem_inf, Subgroup.mem_top, true_and, MonoidHom.mem_ker, cycZ,
        MonoidHom.comp_apply] using h1
    have hl : ∀ k, ∀ t : Ω, t ^ (l ^ k) = 1 → g t = t := fun k => (key g k).1 (by rw [hχ, Units.val_one, map_one])
    have hN : ∀ t : Ω, t ^ N = 1 → g t = t := h2
    obtain ⟨e, N', hndvd, hNe⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne N) l (Fact.out : l.Prime).one_lt.ne'
    have hcop : Nat.Coprime (l ^ (e + m)) N' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hndvd)
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))] at hx
      exact zero_ne_one hx
    have hxA : x ^ (l ^ (e + m) * N') = 1 := by
      rw [← hx, hNe, pow_add]
      congr 1
      ring
    have h3 : g (x ^ N') = x ^ N' := hl (e + m) _ (by rw [← pow_mul, mul_comm, hxA])
    have h4 : g (x ^ (l ^ (e + m))) = x ^ (l ^ (e + m)) := by
      apply hN
      rw [hNe, ← pow_mul, show l ^ (e + m) * (l ^ e * N') = (l ^ (e + m) * N') * l ^ e by ring, pow_mul, hxA,
        one_pow]
    have hyA : (g x * x⁻¹) ^ (l ^ (e + m)) = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, h4, mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hyB : (g x * x⁻¹) ^ N' = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, h3, mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hy : (g x * x⁻¹) ^ (Nat.gcd (l ^ (e + m)) N') = 1 := pow_gcd_eq_one.2 ⟨hyA, hyB⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hy
    exact (mul_inv_eq_one₀ hx0).1 hy
  · intro M _ b σ hdvd hσ
    have hc := (pow_cyc_char_iff_toZModPow_eq l σ m (((b : ZMod M).val : ℕ) : ZMod (l ^ m))).1 (by
      intro t ht
      rw [ZMod.val_natCast, pow_mod_eq_pow_of_pow_eq_one t _ _ ht]
      apply hσ
      obtain ⟨q, rfl⟩ := hdvd
      rw [pow_mul, ht, one_pow])
    have hmem : ((cyclotomicCharacter Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) - (((b : ZMod M).val : ℕ) : ℤ_[l]) ∈
        RingHom.ker (PadicInt.toZModPow m) := by
      rw [RingHom.mem_ker, map_sub, hc, map_natCast, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    exact hmem
