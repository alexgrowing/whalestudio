import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open NumberField

noncomputable section

def zetaSevenHalves : ℝ :=
  (riemannZeta (7 / 2 : ℂ)).re

def ZetaSevenHalvesBounds.Value.Statement : Prop :=
  riemannZeta (7 / 2 : ℂ) = (zetaSevenHalves : ℂ) ∧
    (1.1267 : ℝ) ≤ zetaSevenHalves ∧ zetaSevenHalves < (1.1268 : ℝ)

def ZetaSevenHalvesBounds.LogBound.Statement : Prop :=
  Real.log zetaSevenHalves ≤ (0.13 : ℝ)

def ZetaSevenHalvesBounds.TwiceLogBound.Statement : Prop :=
  2 * Real.log zetaSevenHalves ≤ (0.26 : ℝ)

def ZetaSevenHalvesBounds.DedekindBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Real.log (dedekindZeta K (7 / 2 : ℂ)).re ≤
      (Module.finrank ℚ K : ℝ) * Real.log zetaSevenHalves

end

end GroundTheory.Heights₂.Theta
