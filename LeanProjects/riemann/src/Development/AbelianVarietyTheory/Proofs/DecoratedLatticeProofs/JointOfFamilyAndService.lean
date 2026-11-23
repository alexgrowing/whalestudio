import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FamAllQ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelOfLinks
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLawsStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem joint_of_famAllQ : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), FamAllQ W → ServedQ W → Joint W := by
  intro hCusp hHC D L hT Gi Gl Kc Yd cX ex W hFam hServ
  obtain ⟨z, hz, hzc, hu⟩ := hFam
  refine ⟨z, hz, hzc, fun u => ?_⟩
  obtain ⟨f, d, hPin, hLaws, hZ, hTail, hDown, hOnto, hComm, hRat⟩ := hu u
  have hMain : MainX f.t := GlobalTheory.T.seesawTransportRelations_of_familyLaws hCusp hHC D _ _ f.t hLaws
  obtain ⟨U, r, c, hr, hU, hc, hRel⟩ :=
    rel_of_links W u f d hLaws.tup hMain hZ hTail hDown hOnto hComm hRat hServ
  exact ⟨d, U, r, c, hPin, hr, hU, hc, hRel⟩

end GlobalTheory.MiTop
