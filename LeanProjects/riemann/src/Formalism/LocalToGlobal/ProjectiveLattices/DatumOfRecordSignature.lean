import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions

def DatDom (D : D7) (j : ℕ) (hI : DatInt D j) : Prop := DomFor D j (efW D j hI)

def datumOfRecord (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (hP : FactPrincipalDatum)
    (hd : DatDom D j (datInt_of hP D j)) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum (hostOfRecord D) :=
  datumOf D j (datInt_of hP D j)
    { unimod := efW_unimod_of hP D j _, rank := latW_rank D j hj, dom := hd }

end Formalism.L2.Pj
