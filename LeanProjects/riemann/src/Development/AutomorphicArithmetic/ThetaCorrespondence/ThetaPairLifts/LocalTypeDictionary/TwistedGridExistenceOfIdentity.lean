import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridExistenceOfFunctoriality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
open scoped TensorProduct nonZeroDivisors Pointwise
namespace GlobalTheory.RowEx.GridExPf
open Formalism.L2.Col GlobalTheory.GridPlaces
variable {D : D7}
end GlobalTheory.RowEx.GridExPf
namespace GlobalTheory.RowEx
open GlobalTheory.RowEx.GridExPf
theorem twisted_grid_existence_of_identity (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : GridEx := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS hQ => ?_⟩⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hS.size
  have hcls : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK := Pm.level_split
  have hPl := exists_places_of_cls T R.toLevCh A.μ0 hS.core.lev (fun k => hcls _ (D.host.g_level k))
    (hcls _ D.host.pde_level.1) (hcls _ D.host.pde_level.2) (leastSplitAuxiliaryPrime_ne_typePrime_of_sizes hS.size) hQ
  obtain ⟨G⟩ := (GlobalTheory.ChiGridModel.nonempty_gridData_iff R.toLevCh A.μ0 hS.core.lev ⟨1, CF, large₂.sc.b⟩).2 hPl
  obtain ⟨W, hW⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hP.weilRepresentationUnitaryPair R hS.core.lev
    hS.core.chain hS.core.models _ G
  haveI := hS.fin
  exact ⟨G, W, hW, GlobalTheory.FunObj.gridChoice_nonempty_of W hS.core.lev Set.finite_univ (GlobalTheory.RowClaim.Test.pde_ne_q hS)
    fun t _ P hP => GlobalTheory.RowClaim.Test.guard hS t P hP⟩
end GlobalTheory.RowEx
end
end
