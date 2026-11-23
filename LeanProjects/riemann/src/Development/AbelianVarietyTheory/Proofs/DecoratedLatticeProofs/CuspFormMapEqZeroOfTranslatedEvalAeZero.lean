import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), IsInfFam θ → (∀ τ, (v₀ τ : M.H τ) ≠ 0) → ∀ T ∈ MultT θ M J χ, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 → T = 0 := by
  intro D X h θ S M J χ t v₀ _ hv₀ T hTm hae
  let T' : MMap M := PiTensorProduct.lift.symm T
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hTm
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ T').1 hT'm
  have hval : T' v₀ = T (PiTensorProduct.tprod ℂ v₀) := by
    simp [T', PiTensorProduct.lift_symm]
  have hf := (hT.aut v₀).cont
  have hleft := (hT.aut v₀).left
  let ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA := iotaX X h
  have hQ : ∀ γ ∈ X.B.I.GFset, ι.symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    refine (Formalism.IndefR.RationalEmbedding.iota_rat D (ι.symm γ)).2 ?_
    show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact GlobalTheory.TranslatedEvalInj.castGA_symm_mem _ γ hγ
  let φ : X.B.I.GA → ℂ := fun x => T' v₀ (ι.symm x * t)
  have hφ : ∀ x, φ x = T' v₀ (ι.symm (x * ι t)) := fun x => by
    simp only [φ, map_mul, ContinuousMulEquiv.symm_apply_apply]
  have hφc : Continuous φ := by
    have e : φ = fun x => T' v₀ (ι.symm (x * ι t)) := funext hφ
    rw [e]
    exact hf.comp (ι.symm.continuous.comp (continuous_mul_right _))
  have hφi : ∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y := by
    intro γ hγ y
    show T' v₀ (ι.symm (γ * y) * t) = T' v₀ (ι.symm y * t)
    rw [map_mul, mul_assoc]
    exact hleft _ (hQ γ hγ) _
  have hae' : φ =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
    have e : φ = evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
      funext x; simp only [φ, evS, hval]; rfl
    rw [e]; exact hae
  have hz := GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hφc hφi hae'
  have hv : T' v₀ = 0 := by
    funext g
    have e := hz (ι (g * t⁻¹))
    simpa [φ] using e
  have hT0 : T' = 0 := GlobalTheory.TranslatedEvalInj.eq_zero_of_value hT v₀ hv₀ hv
  have : T = PiTensorProduct.lift T' := (PiTensorProduct.lift.apply_symm_apply T).symm
  rw [this, hT0, map_zero]

end
