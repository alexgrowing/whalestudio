import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalOfLocalLanglandsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglandsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatakeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BaseChangeClosing

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

theorem conclusion1_of_baseChange : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D),
      CGTrue hL D T → AUTrue hL D T A → SphericalInertData.Conclusion1 D := by
  intro hNT hB hMW hGU hSC hL D T A hCG hAU
  obtain ⟨hP, hS, hSat⟩ := GlobalTheory.T.rec_product_speh_satake hGU hSC hL D.nd D.naut T
  exact GlobalTheory.DefiniteBCFrozen.baseChangeDefinite_of_cmDatum_recLaws D (recT T hL) hNT hB
    (GlobalTheory.DiscreteSpectrumCM.discreteSpectrum_of_discreteSpectrumGL hMW D.host.E) hP hS hSat
    (GlobalTheory.T.cuspidal_of_local_langlands hL D T hCG) (GlobalTheory.T.unitary_of_local_langlands hL D T A hAU)

end GlobalTheory.BaseChangeClosing

end
