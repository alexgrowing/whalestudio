import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliHighestWeightVanishing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
open MvPolynomial Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_highest_weight_vanishing : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k → x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, f ∈ GlobalTheory.KFixIrr.chiOne P Q R S x → (∀ l ∈ f.vars, Formalism.BasicNotions.TH.linePos l = true) → (∀ i j : Fin (P + Q), i < j → GlobalTheory.Capelli.mixedOp ℂ (GlobalTheory.LowIrr.zR P Q R S) (GlobalTheory.LowIrr.yS P Q R S) i j f = 0) ∧ (∀ i : Fin (P + Q), GlobalTheory.Capelli.mixedOp ℂ (GlobalTheory.LowIrr.zR P Q R S) (GlobalTheory.LowIrr.yS P Q R S) i i f = GlobalTheory.LowIrr.kap P Q k k' i • f) ∧ ∀ (c : Fin R) (d : Fin S), ∑ i, MvPolynomial.pderiv (GlobalTheory.LowIrr.zR P Q R S (c, i)) (MvPolynomial.pderiv (GlobalTheory.LowIrr.yS P Q R S (d, i)) f) = 0 := by
  first | exact @GlobalTheory.MixedHW.mixed_hw_harm | exact GlobalTheory.MixedHW.mixed_hw_harm | (intros; apply GlobalTheory.MixedHW.mixed_hw_harm <;> assumption)
