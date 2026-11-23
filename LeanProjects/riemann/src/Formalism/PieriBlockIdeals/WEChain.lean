import Formalism.PieriBlockIdeals.Statement

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

def WEChain : Prop :=
  ∀ (k j t q l h κ : ℕ) (K : Type) [Field K] [CharP K l]
    (U U' V V' : Fin (k + j + t + q) → ℤ) (b b' c c' : ℤ) (kc kp : Fin t → ℤ),
    l.Prime → t + 2 * κ < l →
    StrictAnti U → StrictAnti U' → StrictAnti V → StrictAnti V' →
    (∀ a, 0 ≤ U a) → (∀ a, U' a ≤ (h : ℤ)) → ∑ a, U a = ∑ a, U' a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    (∀ s : Fin t, ∃ a, V a = b' + ((s : ℕ) : ℤ)) →
    (∏ a, (X + C (((U a + c : ℤ)) : K))) = ∏ a, (X + C (((U' a + c : ℤ)) : K)) →
    (∏ a, (X + C (((V a + c' : ℤ)) : K))) = ∏ a, (X + C (((V' a + c' : ℤ)) : K)) →
    (∀ s, |kc s| ≤ (κ : ℤ)) → (∀ s, |kp s| ≤ (κ : ℤ)) →
    Multiset.map (fun s : Fin t => ((b + ((s : ℕ) : ℤ) - kc s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun a => ((U' a : ℤ) : ZMod l)) Finset.univ.val →
    Multiset.map (fun s : Fin t => ((b' + ((s : ℕ) : ℤ) - kp s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun a => ((V' a : ℤ) : ZMod l)) Finset.univ.val →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ) + (l : ℤ) * kp s - kc s) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) ≤
      (q : ℤ) * h +
        ((l : ℤ) * (mwCount l b' t κ (Finset.univ.image V) : ℤ) +
          (mwCount l b t κ (Finset.univ.image U) : ℤ)) * ((t : ℤ) + 2 * κ)

end Formalism.CohomologicalDescent
