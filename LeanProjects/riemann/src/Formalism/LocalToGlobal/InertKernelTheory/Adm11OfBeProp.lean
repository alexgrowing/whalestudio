import Formalism.LocalToGlobal.InertKernelTheory.StatementZ

noncomputable section

namespace Formalism.L2.KerInert

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def Adm11OfBeProp : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X), BeProp p Y.be → adm11 D X Y

end Formalism.L2.KerInert
