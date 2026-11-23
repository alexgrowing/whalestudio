import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionMemSpanLocalSchrodingerModelsSplitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearModelFourierTransformExchangeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentOfIdelicCharacterAgreementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFramesReadSplitPlaceUnitaryGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinModSpan

theorem isComp_mul_inv {E : Type} [Field E] [NumberField E] {μ η : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {μw ηw : (w.adicCompletion E)ˣ →* ℂˣ} (hμ : IsComp μ w μw) (hη : IsComp η w ηw) :
    IsComp (μ * η⁻¹) w (μw * ηw⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 := hμ.1
    have h2 := hη.1
    unfold GlobalTheory.SmGL.IsSmoothChar at h1 h2 ⊢
    have h3 : IsOpen (((μw.ker ⊓ ηw.ker : Subgroup _)) : Set (w.adicCompletion E)ˣ) := h1.inter h2
    exact Subgroup.isOpen_mono (H₁ := μw.ker ⊓ ηw.ker) (fun y hy => by
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hy ⊢
      simp [hy.1, hy.2]) h3
  · simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ.2 x, hη.2 x]
    rfl

theorem main : ∀ (D : D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ χV χW om, Formalism.IndefR.Datum.IsWeilDatumO ψ V W χV χW om → ∀ μ η : HChar D.host.E, Formalism.IndefR.Links.ChrEq χV μ → Formalism.IndefR.Links.ChrEq χW (μ * η⁻¹) → ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ V W f → f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)), LinearMap.range ι := by
  intro D ψ V W n r PV PW hF hV hW χV χW om hom μ η hμ hη s μw ηw hμw hηw f hf
  obtain ⟨p, hpe, hpr, FS, FT, c, hc, hci, hlocV, hlocW⟩ := GlobalTheory.T.standardFrames_read_splitPlace_unitaryGroup D V W n r PV PW hF hV hW s
  have cV := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χV μ hμ μw hμw
  have cW := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χW (μ * η⁻¹) hη (μw * ηw⁻¹) (isComp_mul_inv hμw hηw)
  obtain ⟨τ, hτ, hτom⟩ := GlobalTheory.T.linearModel_fourier_transform_exchange (s.w.adicCompletion D.host.E) n r
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have h2 := GlobalTheory.T.thetaFunction_mem_span_localSchrodingerModels_split D _ p (Fin r) (Fin n) V W FS FT ψ hom.std f hf
  refine (iSup₂_le fun Tm hTm => ?_ : (⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm) ≤ _) h2
  have hr : LinearMap.range Tm = LinearMap.range (Tm ∘ₗ τ) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hτ, Submodule.map_top]
  rw [hr]
  refine le_iSup₂_of_le (f := fun (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)) => LinearMap.range ι) (Tm ∘ₗ τ) ⟨?_, fun Φ => hTm.theta _⟩ le_rfl
  refine ⟨c, hc, hci, fun h g hh hg Φ Φ' hΦ => ?_⟩
  have hΦ'' : Φ'.1 = GlobalTheory.SplitWeil.om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) Φ.1 := hΦ
  have key := hOm (s.w.adicCompletion D.host.E) p ψ V W χV χW om hom μw (μw * ηw⁻¹) cV cW (Fin r) (Fin n) FS FT Tm hTm
    (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g))
    (hlocV h hh) (hlocW g hg) (τ Φ)
    (((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) : ℂˣ) : ℂ) • τ Φ') (by
      rw [Submodule.coe_smul, hτom μw _ _ Φ Φ' hΦ'']
      congr 2
      simp [mul_inv_rev, mul_comm])
  simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
  show om (PV.ψ h, PW.ψ g) (Tm (τ Φ)) = _
  rw [key, map_smul]

end GlobalTheory.LinModSpan
