import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.QuadraticCharTwistOfExistsOfInfinity
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ValuationLeOneOfInteger
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem satSplit : SatSplit := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hD a π P hP B hB
  obtain ⟨i, hi, hi', hiv⟩ := splitIso_holds K M Ω A v w hv hw hD
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL K a π v
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL M a P w
  obtain ⟨e, he⟩ := hP v w i hi hi' σ σ' hσ hσ'
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  have hq : normV w = normV v ^ 1 := degOf K M Ω A v w hv hw (fun τ hτ => hD τ (Ine_le_Dec A hτ)) φ 1 one_pos hφ
    fun k => ⟨fun _ => one_dvd k, fun _ => hD _ (pow_mem (show φ ∈ Dec (F := K) A from hφ.1) k)⟩
  rw [pow_one] at hq
  refine ((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake M a P w σ' hσ').1 B).2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hiv ?_ e (fun g x => (he g x).symm)
    (((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake K a π v σ hσ).1 B).1 hB))
  first | exact hq | (unfold normV at hq; simp only [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hq)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
