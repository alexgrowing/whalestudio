import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5.Dense

theorem exists_near_root {Ωl : Type} [Field Ωl] [CharZero Ωl] (v : Valuation Ωl ℝ≥0)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (e : Ωl) (t : ℝ≥0) (Q : ℤ[X])
    (h : v (Q.eval₂ (Int.castRingHom Ωl) e) < v (Q.leadingCoeff : Ωl) * t ^ Q.natDegree) :
    ∃ a : Ω, v (e - j a) < t := by
  haveI : CharZero Ω := j.charZero
  by_contra hcon
  push_neg at hcon
  set R : Polynomial Ω := Q.map (Int.castRingHom Ω) with hR
  have hinj : Function.Injective (Int.castRingHom Ω) := Int.cast_injective
  have hdeg : R.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj Q
  have hlc : R.leadingCoeff = (Q.leadingCoeff : Ω) := leadingCoeff_map_of_injective hinj Q
  have hcard : Multiset.card R.roots = R.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have h1 : Q.eval₂ (Int.castRingHom Ωl) e = R.eval₂ j e := by
    rw [hR, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have h2 : R.eval₂ j e = (Q.leadingCoeff : Ωl) * (R.roots.map fun a => e - j a).prod := by
    conv_lhs => rw [← hprod]
    rw [eval₂_mul, eval₂_C, eval₂_multiset_prod, Multiset.map_map, hlc, map_intCast]
    simp
  rw [h1, h2, map_mul, map_multiset_prod, Multiset.map_map] at h
  have h3 : t ^ Q.natDegree ≤ (R.roots.map (v ∘ fun a => e - j a)).prod := by
    have := Multiset.pow_card_le_prod (s := R.roots.map (v ∘ fun a => e - j a)) (a := t) (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
      exact hcon a)
    rwa [Multiset.card_map, hcard, hdeg] at this
  exact absurd h (not_lt.2 (by gcongr))

theorem exists_approx {p : ℕ} [Fact p.Prime] (P : ℤ_[p][X]) (N : ℕ) :
    ∃ (Q : ℤ[X]) (R : ℤ_[p][X]), Q.natDegree ≤ P.natDegree ∧
      P = Q.map (Int.castRingHom ℤ_[p]) + C ((p : ℤ_[p]) ^ N) * R := by
  have h : ∀ x : ℤ_[p], ∃ (m : ℤ) (r : ℤ_[p]), x = m + (p : ℤ_[p]) ^ N * r := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec N x)
    exact ⟨PadicInt.appr x N, r, by push_cast; linear_combination hr⟩
  choose m r hmr using h
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), monomial i (m (P.coeff i)),
    ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (r (P.coeff i)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  · rw [Polynomial.map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [P.as_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_monomial, C_mul_monomial, ← map_add, eq_intCast, ← hmr]

theorem exists_cong : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a : Ω, IsInt p (j a) ∧ Cong p k e (j a) := by
  intro p hp Ωl _ _ hclo Ω _ _ j k e he ⟨P, hP0, hP⟩
  obtain ⟨v, hv, -, hp0, hp1⟩ := exists_valuation_isInt p Ωl hclo
  haveI : CharZero Ωl := Basic.charZero_of_isClo hclo
  have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
  have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
  have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
  have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  have hc : φ P.leadingCoeff ≠ 0 := by
    rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
    exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
  have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
    (a := v (φ P.leadingCoeff) * (v (p : Ωl) ^ k) ^ P.natDegree) (by positivity) hp1
  have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
  have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
    hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
  obtain ⟨Q, R, hdeg, hQR⟩ := exists_approx P N
  have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
    intro y hy
    rw [map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le hy
  have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
    have := congrArg (fun S => φ (coeff S P.natDegree)) hQR
    simp only [coeff_add, coeff_C_mul, coeff_map, map_add, map_mul, eq_intCast, map_intCast] at this
    rw [map_pow, map_natCast] at this
    exact this
  have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
    rw [eq_sub_of_add_eq hco.symm]
    exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
  have hQ0 : Q.coeff P.natDegree ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, map_zero] at hvQ
    exact hvc.ne hvQ
  have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
  have hRe : v (R.eval₂ φ e) ≤ 1 := by
    rw [eval₂_eq_sum_range]
    refine Valuation.map_sum_le v fun i _ => ?_
    rw [map_mul, map_pow]
    exact mul_le_one₀ (hφint _) zero_le (pow_le_one₀ zero_le ((hv _).2 he))
  have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
    rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
      RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
    exact eq_neg_of_add_eq_zero_left hPe
  obtain ⟨a, ha⟩ := exists_near_root v j e (v (p : Ωl) ^ k) Q (by
    rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
    exact (hsmall _ hRe).trans_lt hN)
  refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
  · rw [show j a = e - (e - j a) by ring]
    exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
  · rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ ha.le zero_le
  · field_simp

end GlobalTheory.K5.Dense
