import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepDefs

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

def KeyStartRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → l = d → ∃ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w

end PI.UnitaryGroupMassFormula.UnimodLocStd
