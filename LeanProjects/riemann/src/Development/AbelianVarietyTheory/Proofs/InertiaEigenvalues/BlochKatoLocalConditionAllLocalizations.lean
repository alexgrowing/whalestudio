import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllPrimesOfBlochKato
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.AdmBK

theorem litGoodO_all : LitGoodO := fun l _ LL => (GlobalTheory.LocalIntegers.good_integers l LL).1

theorem blochKato_dimFormula_all_finiteExt_coeffField (D : D7) : TruncatedSeriesCountingBounds.adm8 D := fun l _ K LL _ =>
  GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL

theorem admBK_loc_of_blochKato_tateDuality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admBK i := by
  intro hBK hTD hEC D i
  exact bloch_kato_annihilators_of D i (GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hBK hTD hEC D)
    (fun l _ K => GlobalTheory.TateTop.tateH2_of_duality_loc hTD l (D.loc l) K) (blochKato_dimFormula_all_finiteExt_coeffField D) litGoodO_all

end GlobalTheory.AdmBK
