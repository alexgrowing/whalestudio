import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.WuDecay

noncomputable section

set_option linter.dupNamespace false

namespace Formalism.L2.SG.ConcreteSettingExists

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting

def GapHyp (D : D7) : Prop :=
  1801 ≤ D.R.r ∧ ∀ (τ : D.what₂.Tau) (j : Fin D.R.m) (h : j.1 + 1 < D.R.m),
    16 * (D.R.r : ℚ) ^ 19 ≤ (D.hc τ).b ⟨j.1 + 1, h⟩ - (D.hc τ).b j

def ConcreteSettingExists (D : D7) : Prop :=
  GapHyp D → ∃ X : HidaSetting D, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    X.MeasTie hb ∧ Formalism.L2.SG.WuDecay.WuDecay X ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I)

end Formalism.L2.SG.ConcreteSettingExists
