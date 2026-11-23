import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticRiemannRochAbelianOfPrintedStatement

namespace GlobalTheory

theorem arithRiemannRochAbelian_of_knownResults_known :
    GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch →
      GlobalTheory.Published.ArithRiemannRochAbelian :=
  GlobalTheory.T.arithmetic_riemann_roch_abelian_of_quoted

end GlobalTheory
