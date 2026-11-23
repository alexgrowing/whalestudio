import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSPackIntegrable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalBesselUniquenessHolds

section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.SRe
theorem exists_sPack_integrable_alt :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim →
      ∀ (D : D7) (F : ∀ u, Forms0 D u), GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D →
        ∃ P : SPack D F, Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) := by
  intro hSW hRF D F hG hL
  obtain ⟨X, hb, ψ, Y, hF, tr, hinst, hpin, hmt, hch, hstd, hmc, hlc, hint, hu⟩ :=
    _root_.GlobalTheory.T.local_bessel_uniqueness_holds hSW hRF D F hG hL
  obtain ⟨G⟩ := GlobalTheory.rowDict_goodOp_nonempty D X
  exact ⟨⟨X, hb, Y, hF, ψ, hmt, hch, hstd, hmc, hlc, tr, fun u => (hu u).2.1, fun u => (hu u).2.2.1,
    fun u => (hu u).1, fun u => (hu u).2.2.2, hinst, G, hpin⟩, hint⟩
end GlobalTheory.Mem.SRe
end
