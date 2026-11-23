import Formalism.LocalToGlobal.HermitianColumns.TiedQC
import Formalism.LocalToGlobal.UnitaryNorms.CharDiv

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Herm

abbrev TwistedCharacterData {D : D7} {C : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (Tp : Formalism.L2.Host.TupTied D C nch) : Type 1 :=
  TwChTied D (fun μ v => Tp.InQ' μ v)

end Formalism.L2.Herm

end
