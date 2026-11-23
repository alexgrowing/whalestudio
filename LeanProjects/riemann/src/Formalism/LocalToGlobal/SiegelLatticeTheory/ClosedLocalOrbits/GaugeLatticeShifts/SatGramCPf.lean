import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActR
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoSEnd

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

theorem satGramC'_of (hL : Formalism.L2.SG.Pf.SatGramActL.LeftActC') (hR : Formalism.L2.SG.Pf.SatGramActR.RightActC') :
    SatGramC' := by
  intro D X Y u u' hI hA hF
  have h1 := Set.mem_insert (Y.tO u u').genSet {(Y.tO u u').ngSet, (Y.tO u u').degSet}
  have h2 : (Y.tO u u').ngSet ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  exact ⟨Formalism.L2.SG.Pf.SatGram.satGram_of (hL := hL D X Y u u' hI hA hF _ h1) (hR := hR D X Y u u' hI hA hF _ h1),
    Formalism.L2.SG.Pf.SatGram.satGram_of (hL := hL D X Y u u' hI hA hF _ h2) (hR := hR D X Y u u' hI hA hF _ h2)⟩

theorem leviOntoC_holds : LeviOntoC := fun _ _ Y u => Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u)

theorem normExpSatC'_of_acts (hN : NeatC) (hM : MassAC) (hL : Formalism.L2.SG.Pf.SatGramActL.LeftActC')
    (hR : Formalism.L2.SG.Pf.SatGramActR.RightActC') : NormExpSatC' :=
  normExpSatC'_of hN leviOntoC_holds hM (satGramC'_of hL hR)

end Formalism.L2.SG.NormCut
