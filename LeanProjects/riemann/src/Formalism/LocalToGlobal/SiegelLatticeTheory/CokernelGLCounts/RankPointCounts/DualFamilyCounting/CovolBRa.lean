import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBR

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def aaLbS (b : Fin D.R.rS) : Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}

def TrDetUnimod : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS) {N : ℕ}
    (m : Module.Basis (Fin N) ℤ ((aaLbS X b).restrictScalars ℤ)),
    N = Module.finrank ℚ D.host.E * (D.R.k + 1) →
    |(Matrix.of fun i j => Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V))).det| =
      |(discr D.host.E : ℚ)| ^ (D.R.k + 1) * (FractionalIdeal.absNorm (aaD D b) : ℚ) ^ (2 * (D.R.k + 1))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
