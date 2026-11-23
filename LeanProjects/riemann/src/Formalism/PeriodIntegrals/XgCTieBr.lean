import Formalism.LocalToGlobal.Columns.GoodXgTie
import Formalism.PeriodIntegrals.XgNamed

namespace PI

def XgCTieBr : Prop :=
  PI.XgNamed.BrauerSplit →
  ∀ {X : Formalism.L2.Col.Fields} (Pr : Formalism.L2.Col.Primes X) {m : ℕ} (Ch : Formalism.L2.Col.Chars X Pr m) (r : ℕ)
    [∀ i, Fact (Pr.g i).Prime] (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ)
    (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i)),
    Formalism.L2.Col.XgCTie Pr Ch r σ teich ζ

end PI
