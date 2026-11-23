import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.AntitoneOfMemInterl

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

theorem gtChar_zero {K : Type*} [Field K] : ∀ (n : ℕ) (t : Fin n → K), gtChar n 0 t = 1
  | 0, _ => rfl
  | n + 1, t => by
    rw [gtChar]
    have h : interl (0 : Fin (n + 1) → ℤ) = {0} := by
      ext mu
      simp only [interl, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · intro h; funext i; have := h i; simp only [Pi.zero_apply]; omega
      · rintro rfl i; simp
    rw [h, sum_singleton, gtChar_zero n]
    simp [wsum]

def IsGTFamily {K : Type*} [Field K] (ch : (n : ℕ) → (Fin n → ℤ) → (Fin n → K) → K) : Prop :=
  (∀ (lam : Fin 0 → ℤ) (t : Fin 0 → K), ch 0 lam t = 1) ∧
    ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ), Antitone lam → ∀ t : Fin (n + 1) → K, (∀ i, t i ≠ 0) →
      ch (n + 1) lam t =
        ∑ mu ∈ interl lam, ch n mu (fun i => t i.castSucc) * t (Fin.last n) ^ (wsum lam - wsum mu)

end ReciprocityTheory.ChartRestriction.TR.Weyl
