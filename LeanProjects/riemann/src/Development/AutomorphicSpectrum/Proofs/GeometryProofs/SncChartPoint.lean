import Mathlib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

def SncChart {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (e : ℕ) (h : Ω) : Prop :=
  ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ A) ∧ (∀ l, a l ∈ A) ∧ ∑ l, a l * f l = 1 ∧
    ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (f l)⁻¹ (A : Set Ω)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ s : S, (s : Ω) = h → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

end GlobalTheory.CompanionTheory.Ar.SncRes
