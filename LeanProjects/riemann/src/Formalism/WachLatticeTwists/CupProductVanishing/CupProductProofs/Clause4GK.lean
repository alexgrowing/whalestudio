import Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.PropLocGKOf
import Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.H2MapInjectiveStatement
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatClose
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatInv
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatIso

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem clause4GK : CupClauseGK := by
  intro p _ K O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hK hO e hε hA
  obtain ⟨F⟩ := ReciprocityTheory.ChartRestriction.T2.natInv_all_iso hK hO e (ε := ε.comp Dw.subtype) hε
  exact clause4 O A T' G r χ E Dw ε hA ⟨F⟩

end Formalism.RepresentationBoundsCohomology.T2
