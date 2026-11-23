import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescentOfLocalGlobalInputs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace DiscreteGroups.T1.G

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_eq (g : GA E n) :
    GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * PositivityTheory.Rg.BcB.thetaA E n g * (PhiU n (Ad E))⁻¹ := by
  have e : GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g) *
      (PhiU n (Ad E))⁻¹ := rfl
  rw [e]
  congr 2

omit [IsCMField E] in

theorem phiU_ad : PhiU n (Ad E) = ratGL E n (PhiU n E) :=
  (GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU (algebraMap E (Ad E)) n).symm

theorem phiU_eq_phiG : PhiU n (Ad E) = GlobalTheory.CsdFromConj.phiG E n := by
  refine ga_ext ?_ ?_
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CsdFromConj.toUnits_PhiK, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]

theorem rt_phiU_inv_mem (π : CuspSub E n) {φ : Sm E n} (hφ : φ ∈ π.V) : rt E n (PhiU n (Ad E))⁻¹ φ ∈ π.V := by
  have h := ((GlobalTheory.CsdFromConj.phiEquiv π).symm ⟨φ, hφ⟩).2
  convert h using 1
  refine Subtype.ext (funext fun x => ?_)
  rw [phiU_eq_phiG]
  simp [GlobalTheory.CsdFromConj.phiEquiv, GlobalTheory.CsdFromConj.phiG, CuspSub.op, mul_assoc]
  show φ.1 _ = φ.1 (x * infGL E n (Unitary.toUnits (PhiK E n)⁻¹) * finGL E n (PhiU n (Af E))⁻¹)
  simp only [map_inv, mul_assoc]

theorem isCsd_of_thetaFix {π : CuspSub E n} (h : ThetaFix π) : π.IsCsd := by
  have hp : ∀ φ ∈ π.V, GlobalTheory.ThetaPull.pull E n φ ∈ π.V := by
    intro φ hφ
    obtain ⟨ψ', hψ', e⟩ := h.2 _ (rt_phiU_inv_mem π hφ)
    convert hψ' using 1
    refine Subtype.ext (funext fun g => ?_)
    rw [GlobalTheory.ThetaPull.pull_apply, e, rt_apply, thetaA_eq, phiU_ad, mul_assoc, (π.cusp φ hφ).1.left]
  refine ⟨LinearEquiv.ofInvolutive ((GlobalTheory.ThetaPull.pull E n).toLinearMap.restrict hp)
    (fun φ => Subtype.ext (GlobalTheory.ThetaPull.pull_pull φ.1)), fun o φ => Subtype.ext ?_⟩
  change GlobalTheory.ThetaPull.pull E n (act (thetaOp o) φ.1) = act o (GlobalTheory.ThetaPull.pull E n φ.1)
  exact (GlobalTheory.ThetaPull.act_pull o φ.1).symm

theorem isDiscrete_of_norm {π : CuspSub E n} (hu : π.IsUnitary)
    (hN : ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) : IsDiscrete π.V :=
  isDiscrete_of_cuspSub π fun φ hφ => by
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_isUnitary hu hφ
    exact GlobalTheory.DiscChar.isSqInt_of_bounded (hN φ hφ) (C := C) fun g => by simpa using hC g

theorem reg_of {π : CuspSub E n} (hreg : (CG.mk π).IsRegAlg) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : HasInfCharGL π.V τ m) : ∃ lam : DomWeight n, m = infOfWeight lam := by
  have h1 : (CG.mk π).HasInfChar τ m := hm
  obtain ⟨hnd, hz⟩ := hreg τ
  rw [h1.infChar_eq] at hnd hz
  obtain ⟨lam, hl⟩ := GlobalTheory.WtComb.exists_domWeight_infOf n m hm.1 hnd hz
  exact ⟨lam, hl.symm.trans (GlobalTheory.UnitaryReadTrue.infOf_eq_infOfWeight lam)⟩

theorem oneEx_of (hF : ThetaFixOf) (hU : UnitOf) (hA : Rig.ThetaOfAsc) : OneEx := by
  intro E _ _ _ n hn π hreg hd
  have hT := hF E n hn π hd
  have hu : π.IsUnitary := (CG.isUnitary_mk π).1 (hU E n hn π hd)
  have hD : IsDiscrete π.V := isDiscrete_of_norm hu hT.1
  choose σ hσ using fun w => GlobalTheory.DiscLocEx.exists_isLocCompGL PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E n π.V hD w
  choose m hm using fun τ => PositivityTheory.Rg.Rs.PInfInd2A.exists_hasInfCharGL hD τ
  let D : Pre E n := ⟨1, fun _ => n, by simp, fun _ => π.V, fun _ w => σ w, fun _ τ => m τ, fun _ => hn,
    fun _ => hD, fun _ w => hσ w, fun _ τ => hm τ⟩
  have hcsd : PositivityTheory.Rg.BcN.CsdAsc π.V :=
    ⟨n, 1, π, hu, GlobalTheory.DiscSpec.isNormalised_of_isDiscrete hD, isCsd_of_thetaFix hT,
      PositivityTheory.Rg.Rs.PDich.ascEmb_one ⟨LinearEquiv.refl ℂ π.V, fun _ _ => rfl⟩⟩
  refine ⟨D, ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩, fun τ => ?_, hA E n D fun _ => hcsd⟩
  obtain ⟨lam, hl⟩ := reg_of hreg (hm τ)
  exact ⟨lam, by simpa [D] using hl⟩

end DiscreteGroups.T1.G

end
