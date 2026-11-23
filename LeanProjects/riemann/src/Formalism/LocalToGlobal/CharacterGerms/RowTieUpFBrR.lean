import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ValuationFitting

structure RingPk {C : Type} [Field C] (V : VF C) where
  vm : Valuation C NNReal
  tie : ValTie V vm
  int : vm.Integers V.RR
  pos : 0 < (vm (V.l : C) : ℝ)
  lt : (vm (V.l : C) : ℝ) < 1
  nonunit : ¬ IsUnit ((V.l : ℕ) : V.RR)
  cpl : IsAdicComplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR
  loc : IsLocalRing V.RR
  alg : Algebra ℤ_[V.l] V.RR
  mm : ∀ x : V.RR, V.MM (x : C) → x ∈ IsLocalRing.maximalIdeal V.RR

def RingPkSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → Nonempty (RingPk V)

end UpFBr

end Formalism.L2.FormalSeriesBounds
