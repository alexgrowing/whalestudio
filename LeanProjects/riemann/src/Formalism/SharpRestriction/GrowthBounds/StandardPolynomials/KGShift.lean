import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
import Mathlib

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2

namespace Formalism.MainNotions.ColumnSystems.Pf.Col

section Hom

variable {σ R : Type} [CommRing R]

def HomG (φ : (σ →₀ ℕ) →+ ℕ) (d : ℕ) (P : MvPolynomial σ R) : Prop := ∀ m ∈ P.support, φ m = d

theorem HomG.zero (φ : (σ →₀ ℕ) →+ ℕ) (d : ℕ) : HomG φ d (0 : MvPolynomial σ R) := by
  intro m hm
  simp at hm

theorem HomG.add {φ : (σ →₀ ℕ) →+ ℕ} {d : ℕ} {P Q : MvPolynomial σ R} (hP : HomG φ d P) (hQ : HomG φ d Q) :
    HomG φ d (P + Q) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hP m h
  · exact hQ m h

theorem HomG.sum {φ : (σ →₀ ℕ) →+ ℕ} {d : ℕ} {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ R)
    (h : ∀ i ∈ s, HomG φ d (P i)) : HomG φ d (∑ i ∈ s, P i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using HomG.zero (R := R) φ d) ?_
  intro i s hi ih h
  rw [Finset.sum_insert hi]
  exact HomG.add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem HomG.mul {φ : (σ →₀ ℕ) →+ ℕ} {d d' : ℕ} {P Q : MvPolynomial σ R} (hP : HomG φ d P) (hQ : HomG φ d' Q) :
    HomG φ (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hm)
  rw [map_add, hP a ha, hQ b hb]

theorem HomG.one (φ : (σ →₀ ℕ) →+ ℕ) : HomG φ 0 (1 : MvPolynomial σ R) := by
  intro m hm
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply] at hm
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm), map_zero]

theorem HomG.sign {φ : (σ →₀ ℕ) →+ ℕ} {d : ℕ} {P : MvPolynomial σ R} (hP : HomG φ d P) (n : ℕ) :
    HomG φ d ((-1) ^ n * P) := by
  have hc : ((-1 : MvPolynomial σ R) ^ n) = MvPolynomial.C ((-1 : R) ^ n) := by simp
  intro m hm
  apply hP m
  rw [hc, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)

theorem HomG.prod {φ : (σ →₀ ℕ) →+ ℕ} {κ : Type} (s : Finset κ) (d : κ → ℕ) (P : κ → MvPolynomial σ R)
    (h : ∀ a ∈ s, HomG φ (d a) (P a)) : HomG φ (∑ a ∈ s, d a) (∏ a ∈ s, P a) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using HomG.one (σ := σ) (R := R) φ) ?_
  intro a s ha ih h
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact HomG.mul (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem KG_hom {n : ℕ} (φ : (σ →₀ ℕ) →+ ℕ) (c : ℤ) (hs : ℕ → ℕ) (x : ℕ → Fin n → MvPolynomial σ R) (ω : ℕ → ℕ)
    (hx : ∀ j b, HomG φ (ω j) (x j b)) :
    ∀ (t : ℕ) (J : Finset (Fin n)), HomG φ (∑ j ∈ range t, if hs j = hs (j + 1) then 0 else ω j) (KG c hs x t J)
  | 0, J => by
    show HomG φ _ (extOne J)
    unfold extOne
    split_ifs
    · simpa using HomG.one (R := R) φ
    · exact HomG.zero φ _
  | t + 1, J => by
    have ih := KG_hom φ c hs x ω hx t
    rw [Finset.sum_range_succ]
    by_cases h : hs t = hs (t + 1)
    · rw [KG_eq h, if_pos h, add_zero]; exact ih J
    · rw [if_neg h]
      show HomG φ _ (colStep c (hs t) (hs (t + 1)) (x t) (KG c hs x t) J)
      unfold colStep wedgeR contrR
      split_ifs
      all_goals first
        | omega
        | exact HomG.sum _ _ fun m _ => by
            rw [mul_assoc, add_comm]; exact ((hx t m).mul (ih _)).sign _

end Hom

section Shift

variable {n : ℕ} {P : Type} [CommRing P]

theorem KG_shift (c : ℤ) (hs : ℕ → ℕ) (x : ℕ → Fin n → P) (h0 : hs 0 = hs 1) :
    ∀ t, KG c hs x (t + 1) = KG c (fun j => hs (j + 1)) (fun j => x (j + 1)) t
  | 0 => by rw [KG_eq h0]; rfl
  | t + 1 => by
    show colStep c (hs (t + 1)) (hs (t + 1 + 1)) (x (t + 1)) (KG c hs x (t + 1)) =
      colStep c (hs (t + 1)) (hs (t + 1 + 1)) (x (t + 1)) (KG c (fun j => hs (j + 1)) (fun j => x (j + 1)) t)
    rw [KG_shift c hs x h0 t]

theorem KG_congr (c : ℤ) {hs hs' : ℕ → ℕ} {x x' : ℕ → Fin n → P} :
    ∀ t, (∀ j, j ≤ t → hs j = hs' j) → (∀ j, j < t → x j = x' j) → KG c hs x t = KG c hs' x' t
  | 0, _, _ => rfl
  | t + 1, h1, h2 => by
    show colStep c (hs t) (hs (t + 1)) (x t) (KG c hs x t) = colStep c (hs' t) (hs' (t + 1)) (x' t) (KG c hs' x' t)
    rw [KG_congr c t (fun j hj => h1 j (by omega)) (fun j hj => h2 j (by omega)), h1 t (by omega), h1 (t + 1) le_rfl,
      h2 t (by omega)]

theorem KG_one (c : ℤ) (ν : ℕ → ℤ) (h0 : ν 0 = 0) (hm : ∀ t, ν t ≤ ν (t + 1)) (hs : ℕ → ℕ)
    (hhs : ∀ t, hs t = if c ≤ ν t then 1 else 0) (x : ℕ → Fin 1 → P) :
    ∀ t, KG c hs x t (if 1 ≤ c ∧ c ≤ ν t then {0} else ∅) = ∏ i ∈ range t, if ν i < c ∧ c ≤ ν (i + 1) then x i 0 else 1
  | 0 => by
    have : ¬ (1 ≤ c ∧ c ≤ ν 0) := by rw [h0]; omega
    rw [if_neg this]
    show extOne ∅ = _
    simp [extOne]
  | t + 1 => by
    have ih := KG_one c ν h0 hm hs hhs x t
    have hnn : ∀ t, 0 ≤ ν t := by
      intro t
      induction t with
      | zero => rw [h0]
      | succ t iht => exact le_trans iht (hm t)
    rw [Finset.prod_range_succ, ← ih]
    by_cases h1 : c ≤ ν t
    · have h2 : c ≤ ν (t + 1) := le_trans h1 (hm t)
      have e : hs t = hs (t + 1) := by rw [hhs, hhs, if_pos h1, if_pos h2]
      have hn : ¬ (ν t < c ∧ c ≤ ν (t + 1)) := by omega
      rw [KG_eq e, if_neg hn, mul_one]
      by_cases hc : 1 ≤ c
      · rw [if_pos ⟨hc, h2⟩, if_pos ⟨hc, h1⟩]
      · rw [if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]
    · by_cases h2 : c ≤ ν (t + 1)
      · have hc : 1 ≤ c := by have := hnn t; omega
        have e : hs t < hs (t + 1) := by rw [hhs, hhs, if_neg h1, if_pos h2]; omega
        have hp1 : 1 ≤ c ∧ c ≤ ν (t + 1) := ⟨hc, h2⟩
        have hn2 : ¬ (1 ≤ c ∧ c ≤ ν t) := fun h => h1 h.2
        have hp3 : ν t < c ∧ c ≤ ν (t + 1) := ⟨by omega, h2⟩
        rw [KG_rise_pos hc e, if_pos hp1, if_neg hn2, if_pos hp3]
        unfold wedgeR
        simp [mul_comm, Finset.filter_singleton]
      · have e : hs t = hs (t + 1) := by rw [hhs, hhs, if_neg h1, if_neg h2]
        have hn : ¬ (ν t < c ∧ c ≤ ν (t + 1)) := fun h => h2 h.2
        have hn1 : ¬ (1 ≤ c ∧ c ≤ ν (t + 1)) := fun h => h2 h.2
        have hn2 : ¬ (1 ≤ c ∧ c ≤ ν t) := fun h => h1 h.2
        rw [KG_eq e, if_neg hn, if_neg hn1, if_neg hn2, mul_one]

end Shift

end Formalism.MainNotions.ColumnSystems.Pf.Col
