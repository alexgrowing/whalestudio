import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility

namespace PositivityTheory.HostN

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult NumberField

abbrev HostNum (D : D7) : Prop := HostHyp D

end PositivityTheory.HostN
