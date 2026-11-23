import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.ClsIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.ImgRoots

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem pow_two_pow (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ^ 2 ^ n = 1 := by
  have h : Nat.totient (2 ^ n) ∣ 2 ^ n := by
    rcases n with _ | n
    · simp
    · rw [Nat.totient_prime_pow_succ Nat.prime_two]
      simpa using pow_dvd_pow 2 (Nat.le_succ n)
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one (ZMod.pow_totient u)).trans h)

private theorem pow_ord {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (a : (ZMod N)ˣ) :
    ψ.toUnitHom a ^ orderOf ψ = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
    MulChar.one_apply_coe, Units.val_one]

private theorem half {Γ : Type} [CommGroup Γ] {y : Γ} {m : ℕ} (hm : Odd m) (hy : y ^ m = 1) :
    ∃ x : Γ, x ^ 2 = y ∧ x ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  refine ⟨y ^ (k + 1), ?_, ?_⟩
  · rw [← pow_mul, show (k + 1) * 2 = 2 * k + 1 + 1 by ring, pow_succ, hy, one_mul]
  · rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]

theorem UpperTheory.V.Ws.large₂.eltOdd :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → ∀ s : ℤ, s = 1 ∨ s = -1 → ∃ (g : G ℚ Ω) (m : ℕ), Odd m ∧ l.Coprime m ∧ D.om g = 1 ∧ D.ξ g ^ 2 = D.ψ g ^ s ∧ D.ξ g ^ m = 1 ∧ D.ξ g ≠ 1 := by
  intro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, hB, he, het, hX, ⟨hlB, hle, hodd, hne⟩, hO⟩ s hs
  obtain ⟨-, hψ, -, _, ξ', ξ₀, -, -, hord, hξ⟩ := hO
  have lp : l.Prime := hl.out
  obtain ⟨-, -, -, hpN, hb⟩ := bchiFacts h t hB
  obtain ⟨-, hlo, -, -, -, hlp, -, hb⟩ := hb l lp hG.l_odd hlB
  obtain ⟨-, -, hlN⟩ := hb e he het hle
  obtain ⟨-, ⟨pp, -, pc⟩, -⟩ := UpperTheory.V.pK_pOne_prime_conditions h.chi
  have hdo : orderOf ψ ∣ h.o :=
    (((hostOdd h c.O ψ (h.mem_X.1 hX).1).1 hodd).1).trans (Nat.ordCompl_dvd _ _)
  have hlm : l.Coprime (orderOf ψ) := lp.coprime_iff_not_dvd.2 fun hd => hlo (hd.trans hdo)
  haveI : NeZero l := ⟨lp.ne_zero⟩
  generalize UpperTheory.V.pOne h.chi = p at *
  generalize h.nIII l ψ = n at *
  have hom : ∀ g, Chr.cls ℚ Ω l g = 1 → D.om g = 1 := by
    have hT : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
      have := hG.om_bar σ
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
      exact sub_eq_zero.2 this⟩
    intro g hg
    have hk := ((omT Ω l c).2 D.om hT).2.1
    rw [← MonoidHom.mem_ker, hk]
    exact hg
  obtain ⟨a, ha⟩ : ∃ a : (ZMod h.N)ˣ, ψ.toUnitHom a ≠ 1 := by
    by_contra hc
    push Not at hc
    apply hne
    ext a
    rw [MulChar.one_apply_coe, ← MulChar.coe_toUnitHom, hc a, Units.val_one]
  haveI : NeZero (l * p) := ⟨mul_ne_zero lp.ne_zero pp.ne_zero⟩
  have c1 : h.N.Coprime (l * p) :=
    Nat.Coprime.mul_right (lp.coprime_iff_not_dvd.2 hlN).symm (pp.coprime_iff_not_dvd.2 hpN).symm
  obtain ⟨u, hu, hu'⟩ := UpperTheory.V.Ws.large₂.clsIndep (Ω := Ω) h.N (l * p) c1 a
  have hy : (ψ.toUnitHom a ^ 2 ^ n) ^ s ≠ 1 := by
    have h1 : ψ.toUnitHom a ^ 2 ^ n ≠ 1 := by
      intro h2
      apply ha
      have hc : (2 ^ n).Coprime (orderOf ψ) := (Nat.coprime_two_left.2 hodd).pow_left _
      have := pow_gcd_eq_one.2 ⟨h2, pow_ord ψ a⟩
      rwa [hc.gcd_eq_one, pow_one] at this
    rcases hs with rfl | rfl
    · simpa using h1
    · simpa using h1
  have hym : ((ψ.toUnitHom a ^ 2 ^ n) ^ s) ^ orderOf ψ = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm, pow_mul, pow_ord, one_pow,
      one_zpow]
  obtain ⟨x, hx2, hxm⟩ := half hodd hym
  obtain ⟨b, hb⟩ := UpperTheory.V.Ws.large₂.imgRoots p ξ₀ x (hord ▸ hxm)
  haveI : NeZero (h.N * l * 2 ^ n) := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne _) lp.ne_zero) (by positivity)⟩
  have c2 : p.Coprime (h.N * l * 2 ^ n) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (pp.coprime_iff_not_dvd.2 hpN) ?_) (Nat.Coprime.pow_right _ ?_)
    · exact (Nat.coprime_primes pp lp).2 hlp.symm
    · exact Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) pc
  obtain ⟨v, hv, hv'⟩ := UpperTheory.V.Ws.large₂.clsIndep (Ω := Ω) p (h.N * l * 2 ^ n) c2 b
  have e1 : D.ξ (u ^ 2 ^ n * v) = x := by
    have f1 : Chr.cls ℚ Ω p (u ^ 2 ^ n * v) = b := by
      rw [map_mul, map_pow, hu' p (dvd_mul_left _ _), hv, one_pow, one_mul]
    have f2 : Chr.cls ℚ Ω (2 ^ n) (u ^ 2 ^ n * v) = 1 := by
      rw [map_mul, map_pow, hv' (2 ^ n) (dvd_mul_left _ _), pow_two_pow, one_mul]
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, f1, f2, map_one, mul_one, hb]
  have e2 : D.ψ (u ^ 2 ^ n * v) = ψ.toUnitHom a ^ 2 ^ n := by
    rw [hψ, Chr.dirG, MonoidHom.comp_apply, map_mul, map_pow, hu, hv' h.N ((dvd_mul_right _ _).mul_right _), mul_one,
      map_pow]
  refine ⟨u ^ 2 ^ n * v, orderOf ψ, hodd, hlm, hom _ ?_, by rw [e1, e2, hx2], by rw [e1, hxm], ?_⟩
  · rw [map_mul, map_pow, hu' l (dvd_mul_right _ _), hv' l ((dvd_mul_left _ _).mul_right _), one_pow, one_mul]
  · rw [e1]
    rintro rfl
    exact hy (by rw [← hx2, one_pow])
