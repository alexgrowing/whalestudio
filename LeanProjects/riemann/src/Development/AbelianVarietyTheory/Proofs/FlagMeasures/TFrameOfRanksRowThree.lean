import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem tFrame_of_ranksRow_three : ∀ 𝒞 : FamClass,
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) →
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro 𝒞 h
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := Formalism.L2.SG.OwnFacts.FD.factDsigHC
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  exact Formalism.L2.SG.Pf.SzHypFam.hTF_of_ranks 3 (𝒞 := 𝒞) h

end GlobalTheory
