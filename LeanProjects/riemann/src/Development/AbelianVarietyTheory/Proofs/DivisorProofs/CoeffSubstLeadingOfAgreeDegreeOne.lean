import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

noncomputable section

namespace GlobalTheory
namespace LeadSubst

open MvPowerSeries

variable {σ τ R : Type*} [CommRing R]

def Near (n : ℕ) (P Q : MvPowerSeries τ R) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((n + 1 : ℕ) : ℕ∞) ≤ (P - Q).order

theorem Near.one : Near 0 (1 : MvPowerSeries τ R) 1 := by
  simp [Near]

theorem Near.mul {n m : ℕ} {P Q P' Q' : MvPowerSeries τ R} (h : Near n P Q)
    (h' : Near m P' Q') : Near (n + m) (P * P') (Q * Q') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast; exact (add_le_add h1 h1').trans le_order_mul
  · push_cast; exact (add_le_add h2 h2').trans le_order_mul
  · have e : P * P' - Q * Q' = P * (P' - Q') + (P - Q) * Q' := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h1 h3')
      push_cast; ring
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h3 h2')
      push_cast; ring

theorem Near.prod {a b : σ → MvPowerSeries τ R}
    (h : ∀ s, Near 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Near d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa using (Near.one : Near 0 (1 : MvPowerSeries τ R) 1)
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add]
    exact hf.mul hg
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.degree_single]
    induction n with
    | zero => simpa using (Near.one : Near 0 (1 : MvPowerSeries τ R) 1)
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul (h s)

theorem near_one {u v : MvPowerSeries τ R} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h1 : ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ u = coeff γ v) : Near 1 u v := by
  refine ⟨by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu,
    by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hv, ?_⟩
  refine nat_le_order fun d hd => ?_
  rw [map_sub, sub_eq_zero]
  rcases (show d.degree = 0 ∨ d.degree = 1 by omega) with h | h
  · rw [(Finsupp.degree_eq_zero_iff d).mp h, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hu, hv]
  · exact h1 d h

end LeadSubst

open MvPowerSeries in

theorem coeff_subst_leading :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries τ R) (N : ℕ)
      (f : MvPowerSeries σ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (∀ i (γ : τ →₀ ℕ), γ.degree = 1 → coeff γ (u i) = coeff γ (v i)) →
      (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) →
      ∀ γ : τ →₀ ℕ, (γ.degree < N → coeff γ (subst u f) = 0) ∧
        (γ.degree ≤ N → coeff γ (subst u f) = coeff γ (subst v f)) := by
  intro R _ σ τ _ u v N f hu hv h1 hf γ
  have hn : ∀ s, LeadSubst.Near 1 (u s) (v s) := fun s => LeadSubst.near_one (hu s) (hv s) (h1 s)
  refine ⟨fun hγ => ?_, fun hγ => ?_⟩
  · rw [coeff_subst (hasSubst_of_constantCoeff_zero hu)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : d.degree < N
    · rw [hf d hd, zero_smul]
    · rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega : γ.degree < d.degree))
        (LeadSubst.Near.prod hn d).1), smul_zero]
  · rw [coeff_subst (hasSubst_of_constantCoeff_zero hu),
      coeff_subst (hasSubst_of_constantCoeff_zero hv)]
    refine finsum_congr fun d => ?_
    by_cases hd : d.degree < N
    · rw [hf d hd, zero_smul, zero_smul]
    · congr 1
      have h := coeff_of_lt_order (d := γ) (lt_of_lt_of_le
        (by exact_mod_cast (by omega : γ.degree < d.degree + 1)) (LeadSubst.Near.prod hn d).2.2)
      rwa [map_sub, sub_eq_zero] at h

end GlobalTheory
