import Formalism.SubspaceCounting.StatementW

noncomputable section

namespace Formalism.G0

def DetQuotVal : Prop :=
  ∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (r : ℕ) (vec : ι → Bool)
    (S' : Finset ι) (A : Fin r → ι) (d : ι → ℕ) (H : MvPolynomial (ι × Fin r) K) (m' th : ℕ),
    Function.Injective A → (∀ l, vec (A l) = true) → MultiHom H d → m' ≤ th →
    ValGE vec S' (fun i => d i + m' * (if i ∈ Set.range A then 1 else 0))
      ((detLetters (K := K) A) ^ m' * H) th →
    ValGE vec S' d H (th - m')

end Formalism.G0
