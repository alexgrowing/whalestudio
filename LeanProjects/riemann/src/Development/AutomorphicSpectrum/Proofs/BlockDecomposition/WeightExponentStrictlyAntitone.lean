import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.Wexp

theorem cone_strictAnti {m : ℕ} {l : Fin m → ℤ} (hl : Cone l) : StrictAnti l := by
  have key : ∀ (d : ℕ) (i j : Fin m), (j : ℕ) = i + d + 1 → l j < l i := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have := hl.1 i j (by omega)
      omega
    | succ d ih =>
      intro i j hij
      have hk : (i : ℕ) + d + 1 < m := by have := j.isLt; omega
      have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
      have h2 := hl.1 ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
      omega
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  exact key ((j : ℕ) - i - 1) i j (by omega)

theorem wexp_of_lt {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h : (i : ℕ) < n / 2) :
    wexp n l i = l ⟨i, h⟩ := by
  simp only [wexp, dif_pos h]

theorem wexp_of_rev_lt {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h' : n - 1 - (i : ℕ) < n / 2) :
    wexp n l i = -l ⟨n - 1 - i, h'⟩ := by
  have h : ¬ (i : ℕ) < n / 2 := by have := i.isLt; omega
  simp only [wexp, dif_neg h, dif_pos h']

theorem wexp_of_middle {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h : ¬ (i : ℕ) < n / 2)
    (h' : ¬ n - 1 - (i : ℕ) < n / 2) : wexp n l i = 0 := by
  simp only [wexp, dif_neg h, dif_neg h']

theorem wexp_strictAnti_rev : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l →
    StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  intro n l hl
  have hs := cone_strictAnti hl
  have hp := hl.2
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have hj := j.isLt
    by_cases h1 : (i : ℕ) < n / 2
    · rw [wexp_of_lt l i h1]
      have a := hp ⟨i, h1⟩
      by_cases h2 : (j : ℕ) < n / 2
      · rw [wexp_of_lt l j h2]
        exact hs (Fin.mk_lt_mk.mpr hij')
      · by_cases h3 : n - 1 - (j : ℕ) < n / 2
        · rw [wexp_of_rev_lt l j h3]
          have b := hp ⟨_, h3⟩
          omega
        · rw [wexp_of_middle l j h2 h3]
          omega
    · have h3 : n - 1 - (j : ℕ) < n / 2 := by omega
      rw [wexp_of_rev_lt l j h3]
      have b := hp ⟨_, h3⟩
      by_cases h2 : n - 1 - (i : ℕ) < n / 2
      · rw [wexp_of_rev_lt l i h2]
        have : l ⟨n - 1 - i, h2⟩ < l ⟨n - 1 - j, h3⟩ := hs (Fin.mk_lt_mk.mpr (by omega))
        omega
      · rw [wexp_of_middle l i h1 h2]
        omega
  · intro i
    have hi := i.isLt
    have hr : ((Fin.rev i : Fin n) : ℕ) = n - 1 - i := by
      rw [Fin.val_rev]; omega
    by_cases h1 : (i : ℕ) < n / 2
    · have h' : n - 1 - ((Fin.rev i : Fin n) : ℕ) < n / 2 := by omega
      rw [wexp_of_rev_lt l _ h', wexp_of_lt l i h1]
      congr 2
      apply Fin.ext
      simp only
      omega
    · by_cases h2 : n - 1 - (i : ℕ) < n / 2
      · have h' : ((Fin.rev i : Fin n) : ℕ) < n / 2 := by omega
        rw [wexp_of_lt l _ h', wexp_of_rev_lt l i h2, neg_neg]
        congr 1
        exact Fin.ext hr
      · rw [wexp_of_middle l i h1 h2, wexp_of_middle l _ (by omega) (by omega), neg_zero]

end GlobalTheory.CompanionTheory.Wexp
