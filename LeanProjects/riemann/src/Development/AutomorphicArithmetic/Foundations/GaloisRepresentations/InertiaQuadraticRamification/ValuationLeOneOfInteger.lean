import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem isFrob_pow' {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : G F Ω} (h : IsFrob A q φ) (n : ℕ) :
    IsFrob A (q ^ n) (φ ^ n) := by
  induction n with
  | zero =>
    refine ⟨one_mem _, ?_⟩
    intro x _
    simp
  | succ n ih =>
    refine ⟨pow_mem h.1 _, ?_⟩
    intro x hx
    have hy : A.valuation (φ x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      exact (apply_mem_iff_of_mem_Dec h.1 x).2 hx
    have h1 := ih.2 (φ x) hy
    have h2 := h.2 x hx
    have hz : A.valuation (x ^ q) ≤ 1 := by
      rw [map_pow]; exact pow_le_one' hx q
    have hc1 : A.valuation (∑ i ∈ Finset.range (q ^ n), (φ x) ^ i * (x ^ q) ^ (q ^ n - 1 - i)) ≤ 1 := by
      refine Valuation.map_sum_le _ (fun i _ => ?_)
      rw [map_mul, map_pow, map_pow]
      exact mul_le_one' (pow_le_one' hy _) (pow_le_one' hz _)
    have h3 : A.valuation ((φ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) < 1 := by
      rw [← geom_sum₂_mul (φ x) (x ^ q) (q ^ n), map_mul]
      exact (mul_le_of_le_one_left' hc1).trans_lt h2
    have e : (φ ^ (n + 1)) x - x ^ (q ^ (n + 1))
        = ((φ ^ n) (φ x) - (φ x) ^ (q ^ n)) + ((φ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) := by
      rw [pow_succ, AlgEquiv.mul_apply, pow_succ', pow_mul]
      ring
    rw [e]
    exact Valuation.map_add_lt _ h1 h3

private theorem one_lt_normV_inertia_quadratic_ramification {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    1 < normV w := by
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  show 1 < Nat.card (𝓞 E ⧸ w.asIdeal)
  exact Finite.one_lt_card

theorem degOf : DegOf := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ A v w hv hw hI φ d hd hφ hfix
  obtain ⟨f, hf⟩ := GlobalTheory.WeilRestrict.normV_eq_pow_of_isPlaceOver (K := K) (L := M) hv hw
  have hq : 1 < normV v := one_lt_normV_inertia_quadratic_ramification v
  have hw1 : 1 < normV w := one_lt_normV_inertia_quadratic_ramification w
  have hdf : d ∣ f := by
    haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) (A := Ω) M
    haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed K, inferInstance⟩
    obtain ⟨σ, hσ⟩ := exists_isFrob (F := M) hw
    have hφf := isFrob_pow' hφ f
    rw [← hf] at hφf
    set ρ := GlobalTheory.WeilRestrict.resG K σ with hρ
    have hρD : ρ ∈ Dec A := GlobalTheory.WeilRestrict.resG_mem_Dec hσ.1
    have hτI : ρ * (φ ^ f)⁻¹ ∈ Ine A := by
      show ρ * (φ ^ f)⁻¹ ∈ ValuationSubring.decompositionSubgroup K A ∧
        ∀ x : Ω, A.valuation x ≤ 1 → A.valuation ((ρ * (φ ^ f)⁻¹) x - x) < 1
      refine ⟨mul_mem hρD (inv_mem hφf.1), ?_⟩
      intro x hx
      obtain ⟨y, rfl⟩ : ∃ y, x = (φ ^ f) y := ⟨(φ ^ f).symm x, ((φ ^ f).apply_symm_apply x).symm⟩
      have hyA : A.valuation y ≤ 1 := by
        rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
        exact (apply_mem_iff_of_mem_Dec hφf.1 y).1 hx
      have h1 := hσ.2 y hyA
      have h2 := hφf.2 y hyA
      have e : (ρ * (φ ^ f)⁻¹) ((φ ^ f) y) - (φ ^ f) y
          = (σ y - y ^ normV w) - ((φ ^ f) y - y ^ normV w) := by
        rw [AlgEquiv.mul_apply]
        rw [show (φ ^ f)⁻¹ ((φ ^ f) y) = y from (φ ^ f).symm_apply_apply y]
        rw [hρ, GlobalTheory.WeilRestrict.resG_apply]
        ring
      rw [e]
      exact Valuation.map_sub_lt _ h1 h2
    have hfixτ := hI _ hτI
    rw [← hfix f]
    intro x
    have h1 : (ρ * (φ ^ f)⁻¹) (algebraMap M Ω x) = algebraMap M Ω x := hfixτ x
    have h2 : ρ (algebraMap M Ω x) = algebraMap M Ω x := by
      rw [hρ, GlobalTheory.WeilRestrict.resG_apply]
      exact σ.commutes x
    rw [AlgEquiv.mul_apply] at h1
    have h3 : (φ ^ f)⁻¹ (algebraMap M Ω x) = algebraMap M Ω x := ρ.injective (h1.trans h2.symm)
    calc (φ ^ f) (algebraMap M Ω x) = (φ ^ f) ((φ ^ f)⁻¹ (algebraMap M Ω x)) := by rw [h3]
      _ = algebraMap M Ω x := (φ ^ f).apply_symm_apply _
  have hfd : f ≤ d := by
    have key : ∀ x : 𝓞 M, x ^ (normV v ^ d) - x ∈ w.asIdeal := by
      intro x
      rw [← hw]
      have hint : A.valuation (algebraMap M Ω (x : M)) ≤ 1 :=
        GlobalTheory.InertiaAlmostAll.val_le_one_of_isIntegral A (x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ M Ω))
      have hφd := (isFrob_pow' hφ d).2 _ hint
      rw [(hfix d).2 dvd_rfl x] at hφd
      have e : algebraMap M Ω (((x ^ (normV v ^ d) - x : 𝓞 M)) : M)
          = -(algebraMap M Ω (x : M) - (algebraMap M Ω (x : M)) ^ (normV v ^ d)) := by
        rw [show (((x ^ (normV v ^ d) - x : 𝓞 M)) : M) = (x : M) ^ (normV v ^ d) - (x : M) by push_cast; ring,
          map_sub, map_pow]
        ring
      rw [e, Valuation.map_neg]
      exact hφd
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    letI : Field (𝓞 M ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
    have hR : Nat.card (𝓞 M ⧸ w.asIdeal) = normV v ^ f := hf
    haveI : Finite (𝓞 M ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by
      show normV w ≠ 0
      omega)
    letI := Fintype.ofFinite (𝓞 M ⧸ w.asIdeal)
    have hN : 1 < normV v ^ d := Nat.one_lt_pow (Nat.pos_iff_ne_zero.1 hd) hq
    have hp0 := FiniteField.X_pow_card_sub_X_ne_zero (𝓞 M ⧸ w.asIdeal) hN
    have hsub : (Finset.univ : Finset (𝓞 M ⧸ w.asIdeal)).val ⊆
        (Polynomial.X ^ (normV v ^ d) - Polynomial.X : Polynomial (𝓞 M ⧸ w.asIdeal)).roots := by
      intro a _
      rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact key x
    have h := Polynomial.card_le_degree_of_subset_roots hsub
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hN, Finset.card_univ, ← Nat.card_eq_fintype_card, hR] at h
    exact (Nat.pow_le_pow_iff_right hq).1 h
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hf; omega
    · exact h
  rw [hf, le_antisymm hfd (Nat.le_of_dvd hf0 hdf)]

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
