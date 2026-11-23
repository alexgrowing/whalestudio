import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

def shortW {K : Type} [Field K] (g2 g3 : K) : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -g2 / 4, a₆ := -g3 / 4 }

def ShortInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    (shortW g2 g3).b₂ = 0 ∧ g₂ (shortW g2 g3) = g2 ∧ g₃ (shortW g2 g3) = g3 ∧
    (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2

def WpNumEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.CM.wpNum (g₂ W) (g₃ W) = 1 + X ^ 2 * wpReg W ∧
    Formalism.L2.Th1.CM.wpDen (g₂ W) (g₃ W) = 1 - C (1 / 2 : K) * X ^ 3 * derivative K (wpReg W)

def WpRegInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W W' : WeierstrassCurve K),
    g₂ W = g₂ W' → g₃ W = g₃ W' → wpReg W = wpReg W'

def USerEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    Formalism.L2.Th1.CM.uSer g2 g3 = expSer (shortW g2 g3)

end Formalism.L2.Th1.A
