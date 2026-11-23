import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLiftsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiTypeProof

theorem xiType : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) →
    (∀ i j b, ActRead (rd i j b)) → ρ.LevelOf D.nexp → XiType rd := by
  intro D ρ hρ rd hF hA hL i _ j b Q M hQ s h P _ _ a x hx
  unfold Formalism.MainNotions.IntegralHeckeForms.Fm0
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D _ D.ntw ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have hu : ρ.eG i j b u ∈ (ρ.B i j b).G.P.H := (hL.U_eq i j b u).2 u.2
  obtain ⟨κ, hlift, hsupp, hser⟩ := GlobalTheory.T.thetaSeries_type_under_supported_lifts D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ (hρ.weil_base i j b) _ hu
  have hg := GlobalTheory.UnivGood.univOf_good D _ D.ntw ρ hρ D.nexp i Q M
  have hdet : detChar (Wc D j) ((univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))) κ = 1 := by
    apply Multiplicative.toAdd.injective
    funext PP
    have := GlobalTheory.T.goodTwist_detChar_eq_one_of_supported_typePlaces D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ ⟨{PP.1}, _, _⟩ (hg.2 PP.1 PP.2)
      (hadm.mono (by simpa using PP.2)) _ κ hlift hsupp
    exact congrArg Multiplicative.toAdd this
  apply (hF i j b).injective
  funext g
  change rd i j b (D.nexp.actG i _ b u x) g = rd i j b (((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x) g
  rw [hA i j b u κ hlift, map_smulₛₗ, Pi.smul_apply, hx]
  unfold Setup.xi
  rw [Base.xiCoef_apply, Base.xiCoef_apply, detChar_mul hg.delQ_real, hdet, mul_one]
  refine (hser _ hadm _ h P g).trans ?_
  rw [hL.psiU_eq i j b u hu, smul_eq_mul]
  rfl

end GlobalTheory.XiTypeProof
