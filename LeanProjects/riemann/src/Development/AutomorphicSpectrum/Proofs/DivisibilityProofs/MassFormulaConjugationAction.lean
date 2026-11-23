import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardCount

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section Lin

variable {K : Type} [Fintype K] {ι : K → Type} {σ : Type}
  (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
  (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A : σ → HermLine ι)

theorem arNum_eq_sum_of_subset (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)) (hs : H.support ⊆ s) :
    arNum I P A H = ∑ μ ∈ s, H.coeff μ * arList I P (μ.toMultiset.map A).toList := by
  unfold arNum
  refine Finset.sum_subset hs fun μ _ hμ => ?_
  rw [MvPolynomial.notMem_support_iff.1 hμ, zero_mul]

theorem arNum_add' (H H' : MvPolynomial σ ℝ) :
    arNum I P A (H + H') = arNum I P A H + arNum I P A H' := by
  classical
  rw [arNum_eq_sum_of_subset I P A (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
    arNum_eq_sum_of_subset I P A H (H.support ∪ H'.support) Finset.subset_union_left,
    arNum_eq_sum_of_subset I P A H' (H.support ∪ H'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem arNum_C_mul' (c : ℝ) (H : MvPolynomial σ ℝ) :
    arNum I P A (C c * H) = c * arNum I P A H := by
  have hs : (C c * H).support ⊆ H.support := by
    intro μ hμ
    rw [MvPolynomial.mem_support_iff] at hμ ⊢
    intro h0
    exact hμ (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [arNum_eq_sum_of_subset I P A (C c * H) H.support hs, arNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_C_mul, mul_assoc]

theorem arNum_zero' : arNum I P A (0 : MvPolynomial σ ℝ) = 0 := by
  simp [arNum]

theorem arNum_sum' {α : Type} (s : Finset α) (H : α → MvPolynomial σ ℝ) :
    arNum I P A (∑ a ∈ s, H a) = ∑ a ∈ s, arNum I P A (H a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using arNum_zero' I P A
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, arNum_add', ih]

theorem arNum_monomial' (μ : σ →₀ ℕ) (c : ℝ) :
    arNum I P A (monomial μ c) = c * arList I P (μ.toMultiset.map A).toList := by
  classical
  rw [arNum_eq_sum_of_subset I P A (monomial μ c) {μ} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem arNum_rename' {σ' : Type} (e : σ' → σ) (H : MvPolynomial σ' ℝ) :
    arNum I P A (rename e H) = arNum I P (A ∘ e) H := by
  classical
  induction H using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [MvPolynomial.rename_monomial, arNum_monomial', arNum_monomial',
      show Finsupp.toMultiset (Finsupp.mapDomain e μ) = (Finsupp.toMultiset μ).map e from
        (Finsupp.toMultiset_map _ _).symm, Multiset.map_map]
  | add p q hp hq => rw [map_add, arNum_add', arNum_add', hp, hq]

end Lin

theorem exists_perm_of_ofFn_perm' {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ s : Equiv.Perm (Fin n), v = w ∘ s :=
  _root_.UpperTheory.Reformulated.B.Yde7.main v w h

theorem arList_eq_of_perm {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1))
    {I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    (l : List (HermLine ι)) (L : Fin (D + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hp : l.Perm (List.ofFn L)) : arList I P l = I P (D + 1) L := by
  have key : ∀ (m : ℕ) (v : Fin m → HermLine ι), (List.ofFn v).Perm (List.ofFn L) →
      I P m v = I P (D + 1) L := by
    intro m v h
    have hm : m = D + 1 := by simpa using h.length_eq
    subst hm
    obtain ⟨s, rfl⟩ := exists_perm_of_ofFn_perm' v L h
    exact hI.1 P _ L s hP hL
  refine key l.length l.get ?_
  rwa [List.ofFn_get]

theorem arNum_linear_arList_symm : (∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι ℤ)) (σ : Type) (A : σ → HermLine ι), (∀ H H' : MvPolynomial σ ℝ, arNum I P A (H + H') = arNum I P A H + arNum I P A H') ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), arNum I P A (C c * H) = c * arNum I P A H) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), arNum I P A (∑ a ∈ s, H a) = ∑ a ∈ s, arNum I P A (H a)) ∧ (∀ (μ : σ →₀ ℕ) (c : ℝ), arNum I P A (monomial μ c) = c * arList I P (μ.toMultiset.map A).toList) ∧ ∀ (σ' : Type) (e : σ' → σ) (H : MvPolynomial σ' ℝ), arNum I P A (rename e H) = arNum I P (A ∘ e) H) ∧ (∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (l : List (HermLine ι)) (L : Fin (D + 1) → HermLine ι), (∀ j, IsSmoothHerm (L j)) → l.Perm (List.ofFn L) → arList I P l = I P (D + 1) L) := by
  refine ⟨?_, ?_⟩
  · intro K _ _ ι _ I P σ A
    exact ⟨arNum_add' I P A, arNum_C_mul' I P A, fun α s H => arNum_sum' I P A s H,
      arNum_monomial' I P A, fun σ' e H => arNum_rename' I P A e H⟩
  · intro K _ _ ι _ P D hP I hI l L hL hp
    exact arList_eq_of_perm hP hI l L hL hp

end GlobalTheory.CompanionTheory.Ar.Num
