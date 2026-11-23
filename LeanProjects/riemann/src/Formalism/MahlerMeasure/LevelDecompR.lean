import Formalism.MahlerMeasure.IsIntegral

namespace Formalism.GM.M

open MvPolynomial Finset

def LevelDecompR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ), Function.Injective w → Function.Injective e →
    (∀ c d, w c ≠ e d) → 1 ≤ r →
    ∀ (o n : ℕ) (u : MvPolynomial σ ℚ_[p]), Formalism.GM.BiHom w e o n u →
      (∃ v : ℕ → MvPolynomial σ ℚ_[p],
        (∀ l, Formalism.GM.tieF w e (v l) = 0 ∧ Formalism.GM.BiHom w e (o - l) (n - l) (v l)) ∧
        u = ∑ l ∈ range (min o n + 1), (Formalism.GM.tieE w e ^ l) (v l)) ∧
      (∀ v v' : ℕ → MvPolynomial σ ℚ_[p],
        (∀ l, Formalism.GM.tieF w e (v l) = 0 ∧ Formalism.GM.BiHom w e (o - l) (n - l) (v l)) →
        (∀ l, Formalism.GM.tieF w e (v' l) = 0 ∧ Formalism.GM.BiHom w e (o - l) (n - l) (v' l)) →
        ∑ l ∈ range (min o n + 1), (Formalism.GM.tieE w e ^ l) (v l) =
          ∑ l ∈ range (min o n + 1), (Formalism.GM.tieE w e ^ l) (v' l) →
        ∀ l ≤ min o n, v l = v' l) ∧
      (∀ (l l' : ℕ) (a b : MvPolynomial σ ℚ_[p]), l ≠ l' →
        Formalism.GM.tieF w e a = 0 → Formalism.GM.BiHom w e (o - l) (n - l) a → l ≤ min o n →
        Formalism.GM.tieF w e b = 0 → Formalism.GM.BiHom w e (o - l') (n - l') b → l' ≤ min o n →
        fock p ((Formalism.GM.tieE w e ^ l) a) ((Formalism.GM.tieE w e ^ l') b) = 0)

end Formalism.GM.M
