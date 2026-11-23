import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.ChiOneNoPt
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary GlobalTheory.JumpDictionaryFoundation
theorem main_alt_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D →
    GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D →
    GlobalTheory.PtCore.ChiOneE D i := by
  intro hF D _h0 h2 h5 hB hM i hl w hw L' hL
  obtain ⟨ρ, hρc, haway, habove⟩ :=
    (_root_.UpperTheory.GalS.weak' h2 i).2.2 (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (sOne D) (integral D hB i)
  have hρ := eq_chi D h5 i w hw ρ hρc haway
  obtain ⟨hdR, hwd, -⟩ := habove w hw
  have hun : D.naut.unr (D.naut.wdOf i ρ w) := by
    rw [hwd]; exact (D.naut.unr_tw _ _).2 (hM i hl w hw)
  have hcW : D.naut.IsCrysW i ρ w := (D.naut.wdOf_unrL i ρ w hw hρc hdR).1 hun
  subst hρ
  have hc : Br.IsCrysW D.loc D.nbr i w hw (chiGL D i 1) :=
    (((D.loc_tie i w hw).2.1 1 _ (continuous_chiGL D i 1)).1).1 hcW
  have hR := GlobalTheory.BlockCrys.subDualRules_of_fontaine hF (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
  have hE := GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL L' hL _ _
    ((GlobalTheory.BlockCrys.matCrysAt_iff D i w hw _).2 hc)
  exact GlobalTheory.BlockCrys.isCrys_inv _ (hR.1 _ _) (hR.2 _ _) _
    (GlobalTheory.ChiOneEnl.isCrys_chiE_of_constituent D i w hw L' hL (hR.1 _ _) _ _ (isConstituent_chiGL D i) hE)
end GlobalTheory.ChiOneNoPt
end
end
