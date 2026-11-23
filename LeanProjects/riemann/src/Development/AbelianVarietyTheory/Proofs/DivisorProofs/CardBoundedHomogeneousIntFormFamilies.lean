import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialCountAndBinomialEstimates
open Filter Topology MvPolynomial GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.Count

theorem abs_intCast_le_iff (c : ℤ) {R : ℝ} (hR : 0 ≤ R) :
    |(c : ℝ)| ≤ R ↔ c ∈ Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ) := by
  rw [Finset.mem_Icc, ← abs_le, ← Int.cast_abs, ← Int.le_floor, Int.natCast_floor_eq_floor hR]

theorem coeff_sum_monomial {D q : ℕ} [Fintype {α : Fin (D + 1) →₀ ℕ // α.degree = q}]
    (g : {α : Fin (D + 1) →₀ ℕ // α.degree = q} → ℤ) (β : Fin (D + 1) →₀ ℕ) :
    coeff β (∑ a, monomial a.1 (g a)) = if h : β.degree = q then g ⟨β, h⟩ else 0 := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨β, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Subtype.ext e)
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    rintro rfl
    exact h a.2

theorem coeff_eq_zero_of_isHomogeneous {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ}
    (hP : P.IsHomogeneous q) {β : Fin (D + 1) →₀ ℕ} (hβ : β.degree ≠ q) : coeff β P = 0 := by
  by_contra hc
  exact hβ (by rw [Finsupp.degree_eq_weight_one]; exact hP hc)

end GlobalTheory.HSAmp.Count

open GlobalTheory.HSAmp.Count in
theorem GlobalTheory.HSAmp.card_bounded_forms : ∀ (D q δ : ℕ) (R : ℝ), 0 ≤ R → {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}.Finite ∧ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}.ncard = (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ∧ Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D ∧ Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) = (q + D).choose D ∧ Module.Finite ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) := by
  intro D q δ R hR
  classical
  have hAcard : Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D := by
    rw [GlobalTheory.natCard_degree_eq, Fintype.card_fin, show q + (D + 1) - 1 = q + D by omega,
      Nat.choose_symm_add]
  haveI : Finite {α : Fin (D + 1) →₀ ℕ // α.degree = q} := (Finsupp.finite_of_degree_eq q).to_subtype
  letI : Fintype {α : Fin (D + 1) →₀ ℕ // α.degree = q} := Fintype.ofFinite _
  set S := {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
    ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R} with hS
  let F : S → (Fin δ → {α : Fin (D + 1) →₀ ℕ // α.degree = q} →
      Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ)) :=
    fun T i a => ⟨coeff a.1 (T.1 i), (abs_intCast_le_iff _ hR).1 (T.2.2 i a.1)⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
      apply Subtype.ext
      funext i
      ext β
      by_cases hβ : β.degree = q
      · have := congrArg Subtype.val (congrFun (congrFun h i) ⟨β, hβ⟩)
        simpa [F] using this
      · rw [coeff_eq_zero_of_isHomogeneous (hT.1 i) hβ, coeff_eq_zero_of_isHomogeneous (hT'.1 i) hβ]
    · intro f
      refine ⟨⟨fun i => ∑ a, monomial a.1 ((f i a : ℤ)), fun i => ?_, fun i β => ?_⟩, ?_⟩
      · exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_monomial _ a.2
      · rw [coeff_sum_monomial]
        split_ifs with h
        · exact (abs_intCast_le_iff _ hR).2 (f i ⟨β, h⟩).2
        · simpa using hR
      · funext i a
        apply Subtype.ext
        simp [F, coeff_sum_monomial, a.2]
  let e := Equiv.ofBijective F hF
  have hfin : S.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
  refine ⟨hfin, ?_, hAcard, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_fun, hAcard,
      Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc, Nat.card_eq_fintype_card,
      Fintype.card_fin, ← pow_mul, mul_comm]
    congr 1
    omega
  · rw [homogeneousSubmodule_eq_finsupp_supported]
    exact (Module.finrank_eq_nat_card_basis
      (basisRestrictSupport ℤ {d : Fin (D + 1) →₀ ℕ | d.degree = q})).trans hAcard
  · rw [homogeneousSubmodule_eq_finsupp_supported]
    haveI : Finite {d : Fin (D + 1) →₀ ℕ | d.degree = q} := (Finsupp.finite_of_degree_eq q).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport ℤ {d : Fin (D + 1) →₀ ℕ | d.degree = q})
