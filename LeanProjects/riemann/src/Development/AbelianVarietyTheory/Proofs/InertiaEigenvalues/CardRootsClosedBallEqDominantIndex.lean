import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonLastDominantIndexMulXSubCStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonDominantIndexXSubCMulStatement
open Polynomial
open Classical

namespace GlobalTheory

theorem dominantIndex_prod_X_sub_C (K : Type) [NormedField K] [IsUltrametricDist K]
    (ρ : ℝ) (hρ : 0 < ρ) (s : Multiset K) :
    ∀ c : K, c ≠ 0 →
      (∀ j, ‖(C c * (s.map fun a => X - C a).prod).coeff j‖ * ρ ^ j ≤
        ‖(C c * (s.map fun a => X - C a).prod).coeff (Multiset.card (s.filter fun z => ‖z‖ ≤ ρ))‖ *
          ρ ^ Multiset.card (s.filter fun z => ‖z‖ ≤ ρ)) ∧
      ∀ j, Multiset.card (s.filter fun z => ‖z‖ ≤ ρ) < j →
        ‖(C c * (s.map fun a => X - C a).prod).coeff j‖ * ρ ^ j <
        ‖(C c * (s.map fun a => X - C a).prod).coeff (Multiset.card (s.filter fun z => ‖z‖ ≤ ρ))‖ *
          ρ ^ Multiset.card (s.filter fun z => ‖z‖ ≤ ρ) := by
  induction s using Multiset.induction_on with
  | empty =>
    intro c hc
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.filter_zero,
      Multiset.card_zero, pow_zero, coeff_C_zero]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp
      · rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.mp h)]; simp
    · rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.mp hj)]; simp [hc]
  | cons a s ih =>
    intro c hc
    obtain ⟨h1, h2⟩ := ih c hc
    have heq : C c * ((a ::ₘ s).map fun a => X - C a).prod =
        (X - C a) * (C c * (s.map fun a => X - C a).prod) := by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm]
    rw [heq, Multiset.filter_cons]
    by_cases ha : ‖a‖ ≤ ρ
    · rw [if_pos ha, Multiset.singleton_add, Multiset.card_cons]
      exact GlobalTheory.T.newtonPolygon_lastDominantIndex_mul_X_sub_C K _ a ρ _ hρ ha h1 h2
    · rw [if_neg ha, zero_add]
      exact GlobalTheory.T.newtonPolygon_dominant_index_X_sub_C_mul K _ a ρ _ hρ (not_le.mp ha) h1 h2

theorem card_roots_closedBall_eq_dominantIndex :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  intro K _ _ _ f ρ hρ hf
  have key := dominantIndex_prod_X_sub_C K ρ hρ f.roots f.leadingCoeff
    (leadingCoeff_ne_zero.mpr hf)
  rw [C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree] at key
  exact key

end GlobalTheory
