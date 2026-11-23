import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCMStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeisenbergOperatorBoundedThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormRealCoordinateMatrixHermitianDetNeZStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCoordinateActionUnitaryPreservesHermitianForStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicActionRealCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHomActionRealCoordinatesEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRealPointsFixFiniteAdelicHomsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicAddRealChartPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionSmoothVectorRealHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOfSmoothRealHeisenbergLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfHeisenbergInvariantNormsStatement

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF GlobalTheory.RealWeil

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem ev_fderivF (hc : IsCharAF F ψ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (G : BBF σ JS JT ξ₀ ψ)
    (hG : Sm (rhoVF σ JS JT ξ₀ ψ hc ι) G) (z : IxF F nS nT → ℂ) (w : WOF F E nS nT) :
    (fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z).1 w =
      deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • z)) G.1 w) 0 := by
  have hd : DifferentiableAt ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 :=
    (hG.differentiable (by simp)).differentiableAt
  let L : ↥(BBF σ JS JT ξ₀ ψ) →L[ℝ] ℂ :=
    ((BoundedContinuousFunction.evalCLM ℂ w).comp (BBF σ JS JT ξ₀ ψ).subtypeL).restrictScalars ℝ
  have hline : HasDerivAt (fun t : ℝ => t • z) z 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
  have h2 : HasDerivAt (fun t : ℝ => rhoVF σ JS JT ξ₀ ψ hc ι (t • z) G)
      (fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z) 0 := by
    have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact h
  have h3 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  exact h3.deriv.symm

theorem fderiv_vacF (hc : IsCharAF F ψ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ)
    (G : BBF σ JS JT ξ₀ ψ) (hG : Sm (rhoVF σ JS JT ξ₀ ψ hc ι) G) (hv : IsVacF σ JS JT ξ₀ ψ ι s G.1)
    (z : IxF F nS nT → ℂ) :
    fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z +
      Complex.I • fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 (Complex.I • s *ᵥ z) = 0 := by
  apply Subtype.ext
  ext w
  have h1 := ev_fderivF hc ι G hG z w
  have h2 := ev_fderivF hc ι G hG (Complex.I • s *ᵥ z) w
  have h3 := hv w z
  rw [PositivityTheory.ThKW.jV_apply] at h3
  simp only [Submodule.coe_add, Submodule.coe_smul, BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.coe_smul, Pi.add_apply, smul_eq_mul, Submodule.coe_zero,
    BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  rw [h1, h2]
  exact h3

variable {B : Base F E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}

theorem exists_inf_A (C : Ctx σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f := by
  obtain ⟨good, hS, hT, h0, hξ, hinf, hchart⟩ := C
  obtain ⟨hc, -⟩ := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B good
  obtain ⟨hHh, hHd⟩ := GlobalTheory.T.hermitianFormRealCoordinateMatrix_hermitian_det_ne_zero F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ
  have hheis : GlobalTheory.RealWeil.IsHeis
      (fun x y : IxF F nS nT → ℂ => (star y ⬝ᵥ (HMF JS JT ξ₀ (tauB B)).mulVec x).im)
      (rhoVF σ JS JT ξ₀ B.ψ hc ι) := by
    unfold GlobalTheory.RealWeil.IsHeis
    simp only [GlobalTheory.RealWeilF.rhoVF]
    refine ⟨fun f => ?_, fun u v f => ?_, fun u f => ?_, fun f => ?_⟩
    · rw [iotaVF_zero, rhoBF_zero]
    · rw [rhoBF_rhoBF, iotaVF_add,
        GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart u v]
    · exact norm_rhoBF hc _ f
    · exact (GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions F E σ nS nT JS JT ξ₀ B.ψ hc f).comp (continuous_iotaVF hchart)
  obtain ⟨Ω, hosc, hone1, hcont, hvac⟩ := GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian (IxF F nS nT) (HMF JS JT ξ₀ (tauB B)) hHh hHd
    (↥(BBF σ JS JT ξ₀ B.ψ)) (rhoVF σ JS JT ξ₀ B.ψ hc ι) hheis (GAF σ JS × GAF σ JT) (mMF σ JS JT θ)
    (GlobalTheory.T.realCoordinateAction_unitary_preserves_hermitianForm F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart)
  obtain ⟨hadd, hsmul, hsmp, hone, hmul, hequiv, hcomm7, hnorm⟩ := hosc
  have hSmθ : ∀ x : ↥(BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) →
      GlobalTheory.RealWeil.Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) x := fun x hx =>
    GlobalTheory.T.thetaFunction_smoothVector_realHeisenberg F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart hc x hx
  have hcommA : ∀ u : WOF F E nS nT, Matrix.map u ⇑(infPartF F E) = 0 →
      ∀ (v : IxF F nS nT → ℂ) (z : ↥(BBF σ JS JT ξ₀ B.ψ)),
        rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v z) =
          rhoVF σ JS JT ξ₀ B.ψ hc ι v (rhoBF σ JS JT ξ₀ B.ψ hc u z) := by
    intro u hu v z
    obtain ⟨h1, h2⟩ := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ u (iotaVF ι v) hu (real_iotaVF hchart v)
    simp only [GlobalTheory.RealWeilF.rhoVF]
    rw [rhoBF_rhoBF, rhoBF_rhoBF, h1, h2, add_comm u (iotaVF ι v)]
  have hfix : ∀ (u : WOF F E nS nT) (z : ↥(BBF σ JS JT ξ₀ B.ψ)),
      heisOF σ JS JT ξ₀ B.ψ u ⇑(z : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑(z : BoundedContinuousFunction (WOF F E nS nT) ℂ) → rhoBF σ JS JT ξ₀ B.ψ hc u z = z := by
    intro u z hz
    apply Subtype.ext
    apply DFunLike.coe_injective
    rw [coe_rhoBF, hz]
  have hth : ∀ p (x : ↥(BBF σ JS JT ξ₀ B.ψ)), IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) →
      IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑((Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) := by
    intro p x hx
    have hsm := hSmθ x hx
    obtain ⟨-, ⟨U, hU, hUx⟩, -, -⟩ := hx
    refine GlobalTheory.T.isThetaFun_of_smooth_real_heisenberg_level F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart hc (Ω p x) (hsmp p x hsm)
      ⟨U, hU, fun u hu hu0 => ?_⟩
    have hA : rhoBF σ JS JT ξ₀ B.ψ hc u x = x := hfix u x (hUx u hu hu0)
    have h7 := hcomm7 p (rhoBF σ JS JT ξ₀ B.ψ hc u) (fun v f => hcommA u hu0 v f) x hsm
    rw [hA] at h7
    rw [← coe_rhoBF hc u (Ω p x), ← h7]
  obtain ⟨om, hom⟩ := GlobalTheory.RealWeilF.exists_homF (GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hc) Ω hth
    (fun p x x' hx hx' => hadd p x x' (hSmθ x hx) (hSmθ x' hx'))
    (fun p a x hx => hsmul p a x (hSmθ x hx))
    (fun x hx => hone x (hSmθ x hx))
    (fun p p' x hx => hmul p p' x (hSmθ x hx))
  have hx : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ x : ↥(BBF σ JS JT ξ₀ B.ψ), ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) = f := by
    intro f hf
    have hb := GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hc f hf
    obtain ⟨hq, -, hcf, -⟩ := hf
    exact ⟨GlobalTheory.RealWeilF.toBF f hcf hb hq, rfl⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩,
    fun g hg h hh f hf => ?_, fun g hg h hh w₀ f hf => ?_⟩, fun s hss hpos p hsp f hf hv => ?_⟩
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom p x hf]
    exact hth p x hf
  · obtain ⟨x, rfl⟩ := hx f hf
    have e : (fun p => om p ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) w) = fun p => (↑(Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) w :=
      funext fun p => by rw [hom p x hf]
    rw [e]
    exact (BoundedContinuousFunction.evalCLM ℂ w).continuous.comp
      (continuous_subtype_val.comp (hcont (GlobalTheory.T.continuous_adelicAction_realCoordinates F E σ B good nS nT JS JT θ hinf) x (hSmθ x hf)))
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [show om p ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑((Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) from hom p x hf]
    exact GlobalTheory.T.lintegral_eq_of_heisenbergInvariant_norms F E σ nS nT JS JT ξ₀ B.ψ hc μ 𝓕 hμ h𝓕 x (Ω p x)
      (fun Hs _ _ _ Φ hΦ => hnorm Hs Φ (fun v g => hΦ (iotaVF ι v) g) p x (hSmθ x hf))
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom (g, h) x hf, hone1 (g, h) (mMF_fin θ hg hh) x (hSmθ x hf)]
  · obtain ⟨x, rfl⟩ := hx f hf
    obtain ⟨u, v, hu, rfl⟩ := GlobalTheory.T.exists_finiteAdelic_add_realChartPoint F E nS nT θ ι hchart w₀
    have hθ0 := GlobalTheory.T.theta_function_heisenberg_invariant F E σ B good nS nT JS JT ξ₀ (u + iotaVF ι v) ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) hf
    obtain ⟨y, hy⟩ := hx _ hθ0
    have hyθ : IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(y : BoundedContinuousFunction (WOF F E nS nT) ℂ) := by rw [hy]; exact hθ0
    have hsym := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ u (iotaVF ι v) hu (real_iotaVF hchart v)
    have hyx : y = rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v x) := by
      apply Subtype.ext
      apply DFunLike.coe_injective
      show ⇑(y : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑((rhoBF σ JS JT ξ₀ B.ψ hc u (rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) x)) : BoundedContinuousFunction (WOF F E nS nT) ℂ)
      rw [hy, coe_rhoBF, coe_rhoBF, heisOF_heisOF, hsym.1, AddChar.map_zero_eq_one, one_smul]
    have hsmv : GlobalTheory.RealWeil.Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) (rhoVF σ JS JT ξ₀ B.ψ hc ι v x) := by
      apply hSmθ
      show IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑((rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) x) : BoundedContinuousFunction (WOF F E nS nT) ℂ)
      rw [coe_rhoBF]
      exact GlobalTheory.T.theta_function_heisenberg_invariant F E σ B good nS nT JS JT ξ₀ (iotaVF ι v) _ hf
    rw [← hy, hom (g, h) y hyθ, hyx, hcomm7 (g, h) _ (hcommA u hu) _ hsmv, hequiv (g, h) v x (hSmθ x hf),
      GlobalTheory.RealWeilF.actOF_add, GlobalTheory.T.unitaryRealPoints_fix_finiteAdelicHoms F E σ nS nT JS JT g h hg hh u hu,
      GlobalTheory.T.adelicHomAction_realCoordinates_eq F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart g h v, hom (g, h) x hf]
    have hsym2 := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ u
      (iotaVF ι ((mMF σ JS JT θ (g, h)).mulVec v)) hu (real_iotaVF hchart _)
    show ⇑((rhoBF σ JS JT ξ₀ B.ψ hc u (rhoBF σ JS JT ξ₀ B.ψ hc
      (iotaVF ι ((mMF σ JS JT θ (g, h)).mulVec v)) (Ω (g, h) x))) : BoundedContinuousFunction (WOF F E nS nT) ℂ) = _
    rw [coe_rhoBF, coe_rhoBF, heisOF_heisOF, hsym2.1, AddChar.map_zero_eq_one, one_smul]
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom p x hf, hvac s p hss hpos hsp x (hSmθ x hf) (fun z => fderiv_vacF hc ι s x (hSmθ x hf) hv z)]
    rfl

end PositivityTheory.ThKW

end
