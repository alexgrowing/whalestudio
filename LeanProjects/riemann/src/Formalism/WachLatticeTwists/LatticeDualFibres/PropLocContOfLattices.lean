import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.PropLoc
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ConnTors
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.HOneTorsionFree
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsBasisOfLattice

universe u

namespace Formalism.RepresentationBoundsCohomology.LOC

theorem propLocCont_of_lattices (hEmb : StatQuotEmbeds.{u}) (hDual : StatDualLattice.{u}) :
    StatPropLocCont.{u} := propLocCont_of connTors hEmb hDual

theorem propLocCont : StatPropLocCont.{u} := propLocCont_of_lattices quotEmbeds dualLattice

end Formalism.RepresentationBoundsCohomology.LOC
