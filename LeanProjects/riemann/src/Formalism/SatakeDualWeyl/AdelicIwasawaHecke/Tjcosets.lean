import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsLoc

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped WithZero

namespace Formalism.UG.P

open Formalism.UG

theorem tjcosets_prod_shift (q : ℤ) (j m : ℕ) :
    (∏ i ∈ Finset.range j, (q ^ (i + 1) - 1)) * ∏ i ∈ Finset.range m, (q ^ (j + m - i) - 1) =
      ∏ i ∈ Finset.range (j + m), (q ^ (i + 1) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ', ← add_assoc, Finset.prod_range_succ, ← ih, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i hi => ?_
    congr 2
    omega

theorem tjcosets_cast_gl (q N m : ℕ) (hq : 1 ≤ q) (hm : m ≤ N) :
    ((∏ i : Fin m, (q ^ N - q ^ (i : ℕ)) : ℕ) : ℤ) =
      (q : ℤ) ^ (∑ i ∈ Finset.range m, i) * ∏ i ∈ Finset.range m, ((q : ℤ) ^ (N - i) - 1) := by
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((q ^ N - q ^ i : ℕ) : ℤ)) m,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ N := by have := Finset.mem_range.1 hi; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hi')]
  push_cast
  rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi']

theorem tjcosets_arith (q n j C : ℕ) (hq : 2 ≤ q) (hj : j ≤ n)
    (h : C * ∏ i : Fin (n - j), (q ^ (n - j) - q ^ (i : ℕ)) =
      ∏ i : Fin (n - j), (q ^ n - q ^ (i : ℕ))) :
    (C : ℤ) * ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + m := ⟨n - j, by omega⟩
  rw [Nat.add_sub_cancel_left] at h
  have hq1 : 1 ≤ q := by omega
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  rw [Nat.cast_mul, tjcosets_cast_gl q m m hq1 le_rfl, tjcosets_cast_gl q (j + m) m hq1 (by omega)] at h'
  have hqs : ((q : ℤ) ^ (∑ i ∈ Finset.range m, i)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  have hAm : ∏ i ∈ Finset.range m, ((q : ℤ) ^ (m - i) - 1) = ∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1) := by
    simpa using tjcosets_prod_shift (q : ℤ) 0 m
  have hX : (C : ℤ) * ∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range m, ((q : ℤ) ^ (j + m - i) - 1) := by
    rw [← hAm]
    apply mul_left_cancel₀ hqs
    linear_combination h'
  have s1 := tjcosets_prod_shift (q : ℤ) j m
  have s2 := tjcosets_prod_shift (q : ℤ) m j
  rw [add_comm m j] at s2
  have hAm0 : ∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have : (1 : ℤ) < (q : ℤ) ^ (i + 1) := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < q)) (by omega)
    linarith
  apply mul_left_cancel₀ hAm0
  calc (∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1)) * ((C : ℤ) * ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1))
      = (∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1)) *
          ((C : ℤ) * ∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1)) := by ring
    _ = _ := by rw [hX, s1, ← s2]

section Adic

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

instance tjcosets_isLocalRing : IsLocalRing (Ov F v) :=
  inferInstanceAs (IsLocalRing (v.adicCompletionIntegers F))

theorem tjcosets_finite : Finite (IsLocalRing.ResidueField (Ov F v)) := glint_finite_residueField v

theorem tjcosets_lt_one_iff (x : ℤᵐ⁰) :
    x < 1 ↔ x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
  induction x using WithZero.recZeroCoe with
  | zero => simp
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, WithZero.coe_le_coe]
    change Multiplicative.toAdd a < 0 ↔ Multiplicative.toAdd a ≤ -1
    omega

theorem tjcosets_mem_max (x : Ov F v) :
    IsLocalRing.residue (Ov F v) x = 0 ↔ Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  refine (ValuationSubring.valuation_lt_one_iff (v.adicCompletionIntegers F) x).trans ?_
  have e := (Valuation.isEquiv_valuation_valuationSubring
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).lt_iff_lt (x := (x : v.adicCompletion F)) (y := 1)
  rw [map_one, map_one] at e
  exact e.symm

theorem tjcosets_ne_zero (ϖ : v.adicCompletion F) (hϖ : IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h
  unfold IsUnifV at hϖ
  rw [h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem tjcosets_hmax (ϖ : v.adicCompletion F) (hϖ : IsUnifV F v ϖ) (x : Ov F v) :
    ϖ⁻¹ * (x : v.adicCompletion F) ∈ Ov F v ↔ IsLocalRing.residue (Ov F v) x = 0 := by
  rw [tjcosets_mem_max v x, tjcosets_lt_one_iff, ValuationSubring.mem_toSubring,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hϖ]
  have hc : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) ≠ 0 := WithZero.coe_ne_zero
  constructor
  · intro h
    have := mul_le_mul' (le_refl ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰)) h
    rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul, mul_one] at this
  · intro h
    have := mul_le_mul' (le_refl (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰)⁻¹)) h
    rwa [inv_mul_cancel₀ hc] at this

theorem tjcosets_card_residue :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = qV F v := by
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hmem : ∀ y : v.adicCompletionIntegers F, Valued.v (y : v.adicCompletion F) < 1 →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := fun y hy =>
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).2 hy
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    apply hmem
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.adicCompletion.valued_coe (K := F) (v := v),
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨r, ?_⟩
    simp only [φ, RingHom.comp_apply]
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    apply hmem
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r - x : v.adicCompletionIntegers F) :
        v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, neg_sub, HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
        HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [e, Valuation.map_neg]
    exact hr
  have := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  have hs : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hi : Function.Injective ψ := RingHom.injective ψ
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Equiv.ofBijective ψ ⟨hi, hs⟩)).symm

end Adic

theorem tjcosets_tj_ne_zero {L : Type} [Field L] (O : Subring L) (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0)
    (g : GL (Fin n) L) :
    Tj ℤ n O ϖ j g ≠ 0 ↔
      ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O, g = a * tjcosets_dG n j ϖ hϖ * b := by
  unfold Tj
  rw [Set.indicator_apply_ne_zero]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Pi.one_apply, ne_eq,
    one_ne_zero, not_false_eq_true, and_true]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, Units.ext (by rw [h, Units.val_mul, Units.val_mul, tjcosets_dG_val])⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, tjcosets_dG_val]⟩

theorem Tj_double_coset_decomposition : Formalism.UG.TjCosets := by
  intro F _ _ v n ϖ hϖO hϖ j hj
  have hϖ0 := tjcosets_ne_zero v ϖ hϖ
  haveI := tjcosets_finite v
  have hmax := tjcosets_hmax v ϖ hϖ
  have hset : {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      Tj ℤ n (Ov F v) ϖ j x.out ≠ 0} = {x | ∃ a ∈ GLint (Fin n) (Ov F v),
        ∃ b ∈ GLint (Fin n) (Ov F v), x.out = a * tjcosets_dG n j ϖ hϖ0 * b} := by
    ext x
    exact tjcosets_tj_ne_zero _ n j ϖ hϖ0 x.out
  have hC : Nat.card {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      Tj ℤ n (Ov F v) ϖ j x.out ≠ 0} =
      (tjcosets_par (𝔽 := IsLocalRing.ResidueField (Ov F v)) n j).index := by
    rw [hset]
    exact tjcosets_index (O := Ov F v) n j ϖ hϖO hϖ0 hmax
  letI : Fintype (IsLocalRing.ResidueField (Ov F v)) := Fintype.ofFinite _
  have hcount := tjcosets_ff_count (𝔽 := IsLocalRing.ResidueField (Ov F v)) n j hj
  have hq : Fintype.card (IsLocalRing.ResidueField (Ov F v)) = qV F v := by
    rw [Fintype.card_eq_nat_card]
    exact tjcosets_card_residue v
  have hq2 : 2 ≤ qV F v := by
    rw [← hq]
    exact Fintype.one_lt_card
  rw [hq] at hcount
  rw [hC]
  exact tjcosets_arith (qV F v) n j _ hq2 hj hcount

end Formalism.UG.P
