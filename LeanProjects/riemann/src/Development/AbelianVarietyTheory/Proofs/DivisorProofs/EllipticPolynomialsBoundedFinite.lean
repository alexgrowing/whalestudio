import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicCoeffNatDegreeSubEqMulCmConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorOfValuationLeCofiniteStatement

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.GeoFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_coeff_le {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) (τ : E →+* ℂ) (i : ℕ) :
    ‖τ (P.coeff i)‖ ≤ n.choose i := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) i hm (IsAlgClosed.splits _)
    (fun z hz => (hr τ z hz).le)
  rw [one_pow, one_mul, hd, Polynomial.coeff_map] at h
  exact h

theorem valued_algebraMap (w : Pl E) (k : E) :
    Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
  Formalism.UG.P.levelaf_valued_algebraMap w k

theorem valuation_conjE (w : Pl E) (k : E) :
    w.valuation E (GlobalTheory.SplitPts.conjE E k) = (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E k := by
  have h := (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2 (algebraMap E _ k)
  rw [(conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.1, valued_algebraMap, valued_algebraMap] at h
  exact h

theorem valuation_coeff_le {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {γ : Pl E → WithZero (Multiplicative ℤ)} (hγ0 : ∀ w, γ w ≠ 0)
    {P : E[X]} (hP : P ∈ Ell E n) (hPS : ∀ w ∈ S, (∀ i, Valued.v ((atPl w P).coeff i) ≤ γ w) ∧
      (γ w)⁻¹ ≤ Valued.v ((atPl w P).coeff 0)) (w : Pl E) (i : ℕ) :
    w.valuation E (P.coeff i) ≤ if w ∈ S then γ w else γ (conjSrc (GlobalTheory.SplitPts.conjE E) w) ^ 2 := by
  have hv : ∀ u ∈ S, (∀ j, u.valuation E (P.coeff j) ≤ γ u) ∧ (γ u)⁻¹ ≤ u.valuation E (P.coeff 0) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hPS u hu
    refine ⟨fun j => ?_, ?_⟩
    · have := h1 j
      rwa [atPl, Polynomial.coeff_map, valued_algebraMap] at this
    · rwa [atPl, Polynomial.coeff_map, valued_algebraMap] at h2
  split_ifs with hw
  · exact (hv w hw).1 i
  obtain ⟨hm, hd, -, hr⟩ := hP
  have hrec := GlobalTheory.T.monic_coeff_natDegree_sub_eq_mul_cmConj E n P hm hd hr
  obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
  rcases GlobLev.eq_or_eq_conjSrc huw with rfl | rfl
  · exact absurd hu hw
  set u := conjSrc (GlobalTheory.SplitPts.conjE E) w
  by_cases hi : i ≤ n
  swap
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Valuation.map_zero]
    exact zero_le'
  have hci : P.coeff i = P.coeff 0 * GlobalTheory.SplitPts.conjE E (P.coeff (n - i)) := by
    have := hrec (n - i) (Nat.sub_le n i)
    rwa [Nat.sub_sub_self hi] at this
  have hc0 : P.coeff 0 * GlobalTheory.SplitPts.conjE E (P.coeff 0) = 1 := by
    have := hrec 0 (Nat.zero_le n)
    rw [Nat.sub_zero, ← hd, ← Polynomial.leadingCoeff, hm.leadingCoeff] at this
    exact this.symm
  have hv0 : w.valuation E (P.coeff 0) * u.valuation E (P.coeff 0) = 1 := by
    rw [← valuation_conjE, ← Valuation.map_mul, hc0, Valuation.map_one]
  have hw0 : w.valuation E (P.coeff 0) ≤ γ u := by
    rw [eq_inv_of_mul_eq_one_left hv0]
    have hu0 : u.valuation E (P.coeff 0) ≠ 0 := right_ne_zero_of_mul_eq_one hv0
    exact (inv_le_comm₀ (zero_lt_iff.2 hu0) (zero_lt_iff.2 (hγ0 u))).2 (hv u hu).2
  rw [hci, Valuation.map_mul, valuation_conjE, sq]
  exact mul_le_mul' hw0 ((hv u hu).1 _)

theorem finite_ell_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ γ : Pl E → WithZero (Multiplicative ℤ), (∀ w, γ w ≠ 0) → (∀ᶠ w in cofinite, γ w = 1) →
    {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, (∀ i, Valued.v ((atPl w P).coeff i) ≤ γ w) ∧
      (γ w)⁻¹ ≤ Valued.v ((atPl w P).coeff 0)}.Finite := by
  intro E _ _ _ n S hS γ hγ0 hγ1
  set σ := GlobalTheory.SplitPts.conjE E
  set β : Pl E → WithZero (Multiplicative ℤ) := fun w => if w ∈ S then γ w else γ (conjSrc σ w) ^ 2 with hβ
  have hβ1 : ∀ᶠ w in cofinite, β w ≤ 1 := by
    have h2 : ∀ᶠ w in cofinite, γ (conjSrc σ w) = 1 := (conjSrc_injective σ).tendsto_cofinite.eventually hγ1
    filter_upwards [hγ1, h2] with w h1 h2
    simp only [hβ]
    split_ifs
    · exact h1.le
    · rw [h2, one_pow]
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite E β hβ1
  have hD0' : (D : E) ≠ 0 := by exact_mod_cast hD0
  set r : ℕ → ℝ := fun i => (∑ τ : E →+* ℂ, ‖τ (D : E)‖) * n.choose i with hr
  set X : Fin (n + 1) → Set E := fun i => {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ r i} with hXd
  have hX : ∀ i, (X i).Finite := fun i => Embeddings.finite_of_norm_le E ℂ (r i)
  refine Set.Finite.of_finite_image (f := fun (P : E[X]) (i : Fin (n + 1)) => (D : E) * P.coeff i)
    ((Set.Finite.pi hX).subset ?_) ?_
  · rintro _ ⟨P, ⟨hP, hPS⟩, rfl⟩ i -
    refine ⟨hD _ fun w => valuation_coeff_le hS hγ0 hP hPS w i, fun φ => ?_⟩
    rw [map_mul, norm_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (D : E)‖) (fun τ _ => norm_nonneg _)
      (Finset.mem_univ φ)) (norm_coeff_le hP φ i) (norm_nonneg _)
      (Finset.sum_nonneg fun τ _ => norm_nonneg _)
  · intro P hP Q hQ hPQ
    ext k
    by_cases hk : k ≤ n
    · exact mul_left_cancel₀ hD0' (congrFun hPQ ⟨k, Nat.lt_succ_of_le hk⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.BCT.GeoFin
