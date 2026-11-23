import Formalism.LocalToGlobal.UnitaryNorms.CharExCol
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgValsFin

namespace Formalism.L2.Host

namespace CharEx

theorem algValsFin (L : Type) [Field L] [NumberField L] : AlgValsFin L := algebraic_values_finite L

end CharEx

end Formalism.L2.Host
