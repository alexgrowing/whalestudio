import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq

noncomputable section

namespace Formalism.L2.Col

structure GFamS (K : Type) [Field K] [NumberField K] [StarRing K] extends GFam K where

  sec : ∀ b, (toGFam.mem b).Sec

end Formalism.L2.Col
