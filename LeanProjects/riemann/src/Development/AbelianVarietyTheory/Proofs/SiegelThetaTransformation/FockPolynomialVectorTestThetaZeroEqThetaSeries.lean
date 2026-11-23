import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorOriginEqPolyDerivStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLawsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem bijective_aeval_scale_rename {σ σ' : Type} (e : σ ≃ σ') (c : σ → ℂ) (hc : ∀ v, c v ≠ 0) :
    Function.Bijective
      (MvPolynomial.aeval fun v => MvPolynomial.C (c v) * MvPolynomial.X (e v) :
        MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ) := by
  let F : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
    MvPolynomial.aeval fun v => MvPolynomial.C (c v) * MvPolynomial.X (e v)
  let G : MvPolynomial σ' ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
    MvPolynomial.aeval fun v => MvPolynomial.C (c (e.symm v))⁻¹ * MvPolynomial.X (e.symm v)
  have h1 : F.comp G = AlgHom.id ℂ _ := by
    ext1 v
    simp only [F, G, AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul, MvPolynomial.algHom_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply, Equiv.apply_symm_apply]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hc _), map_one, one_mul]
  have h2 : G.comp F = AlgHom.id ℂ _ := by
    ext1 v
    simp only [F, G, AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul, MvPolynomial.algHom_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply, Equiv.symm_apply_apply]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc _), map_one, one_mul]
  exact (AlgEquiv.ofAlgHom F G h1 h2).bijective

variable {D : D7} {S T : HSp D}

theorem Ctx.fockScale_pos (C : Ctx S T) (τ : D.what₂.Tau) : 0 < fockScale D τ := by
  have h0 : D.host.xi0 ≠ 0 := by
    intro h
    have h1 := C.X.κ0_sign (C.m.e τ)
    rw [C.m.ka, h] at h1
    simp at h1
  have h2 : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 h0)
  unfold fockScale
  have := Real.pi_pos
  positivity

theorem Ctx.toH_bijective (C : Ctx S T) : Function.Bijective C.toH :=
  bijective_aeval_scale_rename (C.m.e.prodCongr ((rowIdx C.hr).symm.prodCongr (Equiv.refl (Fin S.rank))))
    (fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)) fun v => by
      have := C.fockScale_pos v.1
      exact Complex.ofReal_ne_zero.2 (by positivity)

theorem fvec_Th_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), Function.Bijective C.toH ∧ ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsFock B (C.Th (C.xB B) φ) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B (C.Th (C.xB B) φ) Q 0 = thP C.X C.hr C.bas C.idx φ (C.toH Q) (C.xB B) := by
  intro D S T C
  refine ⟨C.toH_bijective, fun B hB φ hφ => ?_⟩
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hZ := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).1
  have hd : Differentiable ℂ (thA C.X C.bas C.idx φ (C.xB B)) := fun z =>
    ((GlobalTheory.SW.theta_holomorphic_weight _ _ C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (fun _ _ => 0)
      (fun _ _ => 0) φ hφ 0 (Submodule.zero_mem _)).2.2.2 _ hx z trivial).differentiableAt
  have hG : ∀ w, IsRealPt w → C.Th (C.xB B) φ w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) *
      thA C.X C.bas C.idx φ (C.xB B) (C.zOf (C.xB B) w) := hZ.2
  refine ⟨fun τ z => ?_, fun Q => GlobalTheory.T.fockPolynomialVector_origin_eq_polyDeriv D S T C B hB _ _ hd hG Q⟩
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  have hth : C.IsTh (annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z (C.Th (C.xB B) φ)) :=
    (h1 _ _ (GlobalTheory.T.heisenbergDerivative_thetaFunction_laws D S T C _ hZ.1 τ z).1
      ((h2 _ (GlobalTheory.T.heisenbergDerivative_thetaFunction_laws D S T C _ hZ.1 τ (cplxO 1 (C.sB B τ) z)).1).1 I)).1
  refine (h1 _ _ hth h0).2 fun w hw => ?_
  rw [(GlobalTheory.T.annihilation_creation_periodCoordinates D S T C B hB _ _ (hd.restrictScalars ℝ) hG τ z _ rfl w hw).1,
    ((hd _).hasFDerivAt.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, Pi.zero_apply]
  rw [← mul_assoc I I, I_mul_I]
  ring

end GlobalTheory.Ker
