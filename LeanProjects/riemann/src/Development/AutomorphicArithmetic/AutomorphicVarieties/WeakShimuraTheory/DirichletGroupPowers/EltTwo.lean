import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

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

private theorem neg_mem_range (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ∈ (proj 2 (2 ^ n)).range := by
  rw [(projFacts (2 ^ n) 2 Nat.prime_two).2.2.2.2.2.1, MonoidHom.mem_ker]
  have e : ordCompl[2] (2 ^ n) = 1 := by
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same, Nat.div_self (by positivity)]
  have : Subsingleton (ZMod (ordCompl[2] (2 ^ n))) := by rw [e]; infer_instance
  exact Subsingleton.elim _ _

theorem UpperTheory.V.Ws.large₂.eltTwo :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → ∃ g ∈ D.Ip 2, D.ξ g = -1 ∧ D.ψ g = 1 ∧ D.om g = 1 := by
  rintro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, -, -, -, -, ⟨-, -, hodd, -⟩, -, hψ, -, hp, ξ', ξ₀, -, hξ', -, hξ⟩
  have hA := hG.pl_over 2 Nat.prime_two
  have hlo : Odd l := hl.out.odd_of_ne_two hG.l_odd
  have hpo : Odd (pOne h.chi) :=
    Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) (pK_pOne_prime_conditions h.chi).2.1.2.2)
  have hom : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hG.om_bar σ⟩
  have h1 : D.Ip 2 ≤ D.om.ker := ((omT Ω l c).2 D.om hom).2.2.2.2.2.1 _ (not_over_odd _ hA hlo)
  have h2 : D.Ip 2 ≤ (Chr.cls ℚ Ω (pOne h.chi)).ker :=
    (Chr.clsFacts ℚ Ω (pOne h.chi)).2.2.2.2 _ (not_over_odd _ hA hpo)
  obtain ⟨g, hg, hc⟩ : (-1 : (ZMod (2 ^ h.nIII l ψ))ˣ) ∈ (D.Ip 2).map (Chr.cls ℚ Ω (2 ^ h.nIII l ψ)) := by
    rw [(compIne Ω (2 ^ h.nIII l ψ) 2 Nat.prime_two _ hA).1]
    exact neg_mem_range _ _
  have h3 : D.ξ g = -1 := by
    have h4 : Chr.cls ℚ Ω (pOne h.chi) g = 1 := h2 hg
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, h4, hc, map_one, one_mul]
    ext1
    rw [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, hξ', Units.val_neg, Units.val_one]
  refine ⟨g ^ orderOf ψ, pow_mem hg _, by rw [map_pow, h3, hodd.neg_one_pow], ?_, h1 (pow_mem hg _)⟩
  rw [hψ, Chr.dirG, MonoidHom.comp_apply, map_pow, map_pow]
  ext1
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
