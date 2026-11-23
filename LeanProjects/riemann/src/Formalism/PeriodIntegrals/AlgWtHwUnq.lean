import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

namespace PI.AlgWtHwUnq

open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

def Stmt : Prop :=
  ∀ (a : AlgWt L n) (τ : L →+* ℂ) (lam lam' : Fin n → ℤ), a.HWAt τ lam → a.HWAt τ lam' → lam = lam'

end PI.AlgWtHwUnq
