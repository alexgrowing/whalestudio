import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem descent_eV_mem_level : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → LevHyp W → (∀ t F, (cxW W).Θ t ((cxW W).jR t (W.Q.F.eV (cxW W).zs t F)) ∈ (cxW W).EEl true) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB hLv t F
  obtain ⟨-, -, -, hC, -⟩ := hB.hyp
  obtain ⟨⟨s, hs⟩, hRZ, gE, hU, hG, h2, hl0, hl1⟩ := hLv
  have hK := RealDat3.kFormR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hJ := RealDat3.jIsoR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hDn := Formalism.IndefR.CxPass.descent_of_types hs hK hJ hRZ hU hG h2 hl0 hl1 true
  have hE := Formalism.IndefR.Links.EvTie.evTie_real ⟨s, hs⟩ W.Q.Rl W.Q.F
  have hV : (cxW W).jR t (W.Q.F.eV (cxW W).zs t F) ∈ (cxW W).V0C W.Q.F.cv true t :=
    Submodule.subset_span ⟨_, hE.1 t F, rfl⟩
  exact hDn t (Submodule.mem_map_of_mem hV)

end GlobalTheory.MiTop

end
