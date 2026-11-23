import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.PeriodIntegrals.BesselMapUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalSettingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDictGoodOpNonempty

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

theorem exists_sPack_integrable :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Formalism.L2.SG.RowsDef.RowsFinDim →
      ∀ (D : D7) (F : ∀ u, Forms0 D u), GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D →
        ∃ P : SPack D F, Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) := by
  intro hSW hBM hRF D F hG hL
  obtain ⟨X, hb, ψ, Y, hF, tr, hinst, hpin, hmt, hch, hstd, hmc, hlc, hint, hu⟩ :=
    GlobalTheory.T.exists_global_setting hSW hBM hRF D F hG hL
  obtain ⟨G⟩ := GlobalTheory.rowDict_goodOp_nonempty D X
  exact ⟨⟨X, hb, Y, hF, ψ, hmt, hch, hstd, hmc, hlc, tr, fun u => (hu u).2.1, fun u => (hu u).2.2.1,
    fun u => (hu u).1, fun u => (hu u).2.2.2, hinst, G, hpin⟩, hint⟩

end GlobalTheory.Mem.SRe
