import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelStabilizers
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelCoupledLastLift

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
  {I : CmpJIn Tw u μ w h Lv}

theorem tieStab_kaAtAny [Fact (D.what₂.places.resChar w).Prime] (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv) (hCh)
    (std) (vp) (unif) (eO) (eO_spec) (dG) (dG_spec) (om) (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (hU : DV.Used D μ) (hS0 : OrbitPlaces.Stab0 D) (j : ℕ) (hj : j ≤ D.R.m) : TieStabAt (Y := Y) u μ (kaAtAny X H Gt Ch hCh).cls j :=
  Formalism.L2.KerInert.SecondKernelStabilizers.stabilizer_any_level D c Tw u μ w h Fl Lv (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt Ch hCh std vp unif eO
    eO_spec dG dG_spec om Y hU hS0 j hj

def fillEmpty (hE : ∀ j, D.R.m < j → IsEmpty (Lv.comp j)) : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j :=
  fun j hj a => (hE j hj).elim a

end Formalism.MainNotions.G.KAat

end
