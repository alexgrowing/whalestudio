import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowCondition
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowAsc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities

theorem speh (h : PositivityTheory.Rg.BcN.BaseChangeIsobaricN) : GlobalTheory.BcSpeh.BcSpeh := bcSpeh_of ascComp (definiteN_of h)

theorem Conclusion1 : DefiniteN → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D),
      CGTrue hL D T → AUTrue hL D T A → SphericalInertData.Conclusion1 D :=
  fun h _ _ => baseChange_preserves_unitary_of ascComp h

end UpperTheory.BaseChangeIdentities

end
