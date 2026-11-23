import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilExistenceOfInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem exists_weilDeligne_of_localInputs (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : WeilEx := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS G => ?_⟩⟩
  obtain ⟨W, hW⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hP.weilRepresentationUnitaryPair R hS.core.lev
    hS.core.chain hS.core.models _ G
  haveI := hS.fin
  exact ⟨W, hW, GlobalTheory.FunObj.gridChoice_nonempty_of W hS.core.lev Set.finite_univ (GlobalTheory.RowClaim.Test.pde_ne_q hS)
    fun t _ P hP => GlobalTheory.RowClaim.Test.guard hS t P hP⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
