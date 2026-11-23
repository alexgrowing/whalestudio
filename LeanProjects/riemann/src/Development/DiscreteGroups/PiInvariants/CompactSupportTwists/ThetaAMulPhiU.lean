import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne

noncomputable section

set_option linter.unusedSectionVars false

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.ContraPair

namespace DiscreteGroups.T1.G

theorem map_PhiU {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (a : ℕ) :
    GeneralLinearGroup.map p (PhiU a R) = PhiU a S := by
  ext i j
  simp [PhiU, GlobalTheory.Tw.Phi, apply_ite]
  split_ifs <;> simp_all

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ratGL_PhiU : ratGL E n (PhiU n E) = PhiU n (Ad E) :=
  map_PhiU (algebraMap E (Ad E)) n

theorem PhiU_Ad : PhiU n (Ad E) = finGL E n (PhiU n (Af E)) * infGL E n (PhiU n (Cinf E)) := by
  conv_lhs => rw [← infGL_mul_finGL (PhiU n (Ad E))]
  rw [map_PhiU, map_PhiU, infGL_comm]

theorem thetaA_mul_PhiU (g : GA E n) :
    GlobalTheory.ThetaPull.thetaA E n g * PhiU n (Ad E) = PhiU n (Ad E) * PositivityTheory.Rg.BcB.thetaA E n g := by
  have e : invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g) = PositivityTheory.Rg.BcB.thetaA E n g := by
    refine Units.ext ?_
    change ((GeneralLinearGroup.map (conjAd E) g)⁻¹ : GL (Fin n) (Ad E)).valᵀ =
      (((g⁻¹ : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ
    rw [← map_inv]
    rfl
  change MulAut.conj (PhiU n (Ad E)) (invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g)) * PhiU n (Ad E) = _
  rw [e, MulAut.conj_apply, inv_mul_cancel_right]

theorem thetaFixOf_of (hG : GlobalTheory.Published.GelfandKazhdanDual) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hM : GlobalTheory.Published.CuspidalMultiplicityOne) : PositivityTheory.Rg.BcB.Desc.ThetaFixOf := by
  intro E _ _ _ n _ π hd
  unfold PositivityTheory.Rg.BcB.Desc.ThetaFix
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired hF E n π (hG E n π) hd
  refine ⟨GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc, fun ψ hψ => ?_⟩
  obtain ⟨T, hT⟩ := hc
  have hiso : (GlobalTheory.ThetaPull.thetaSub π).Iso π := by
    refine ⟨((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V).symm.trans T, fun o φ => ?_⟩
    obtain ⟨χ, rfl⟩ := ((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V).surjective φ
    have e : (GlobalTheory.ThetaPull.thetaSub π).op o ((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V χ) =
        (GlobalTheory.ThetaPull.pull E n).submoduleMap π.V (π.op (thetaOp o) χ) :=
      Subtype.ext (GlobalTheory.ThetaPull.act_pull o χ.1)
    change T (((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V).symm ((GlobalTheory.ThetaPull.thetaSub π).op o
        ((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V χ))) = π.op o (T (((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V).symm
        ((GlobalTheory.ThetaPull.pull E n).submoduleMap π.V χ)))
    erw [e, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hT]
  have hV : (GlobalTheory.ThetaPull.thetaSub π).V = π.V := hM E n _ _ (Quotient.sound hiso)
  have hχ : act (.fin (PhiU n (Af E))) (act (.cpt (PhiK E n)) ψ) ∈ π.V := π.stable _ _ (π.stable _ _ hψ)
  have hp : GlobalTheory.ThetaPull.pull E n (act (.fin (PhiU n (Af E))) (act (.cpt (PhiK E n)) ψ)) ∈
      (GlobalTheory.ThetaPull.thetaSub π).V := Submodule.mem_map_of_mem hχ
  refine ⟨_, hV ▸ hp, fun g => ?_⟩
  have hK : Unitary.toUnits (PhiK E n) = PhiU n (Cinf E) := Units.ext rfl
  have h1 : (GlobalTheory.ThetaPull.pull E n (act (.fin (PhiU n (Af E))) (act (.cpt (PhiK E n)) ψ))).1 g =
      ψ.1 (GlobalTheory.ThetaPull.thetaA E n g * PhiU n (Ad E)) := by
    change ψ.1 (GlobalTheory.ThetaPull.thetaA E n g * finGL E n (PhiU n (Af E)) * infGL E n (Unitary.toUnits (PhiK E n))) = _
    rw [hK, mul_assoc, ← PhiU_Ad]
  rw [h1, thetaA_mul_PhiU, ← ratGL_PhiU]
  exact (π.cusp ψ hψ).1.left _ _

end DiscreteGroups.T1.G

end
