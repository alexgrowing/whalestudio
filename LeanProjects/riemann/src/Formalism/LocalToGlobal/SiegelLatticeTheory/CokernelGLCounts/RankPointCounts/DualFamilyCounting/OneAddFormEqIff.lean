import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix

open Matrix Formalism.HermitianLattices.Ext.L3

namespace Formalism.L2.SG.Pf.discriminantGroupCounts

section Abstract

variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]

def phiH (H Y : Matrix m m A) : Matrix m m A := Y + Yᴴ + Yᴴ * H * Y

end Abstract

end Formalism.L2.SG.Pf.discriminantGroupCounts
