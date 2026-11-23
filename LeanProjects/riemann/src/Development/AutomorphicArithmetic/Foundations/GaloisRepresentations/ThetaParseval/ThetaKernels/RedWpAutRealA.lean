import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutRealA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StandardAdditiveCharacterSign
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HermitianFormMatrixSelfadjoint
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartThetaEquivariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianVector
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousMomentMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaFunctionHeisenbergTranslate
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ActOFIotaVFEqIotaVFMulVec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF GlobalTheory.RealWeil
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}
variable {B : Base F E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem exists_inf_A_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f := by
  have hB := C.good
  have hc : IsCharAF F B.ψ := (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB).1
  have hθ := C.inf
  have hι := C.chart
  have hS := C.hS
  have hT := C.hT
  have hξ := C.h0
  have hξσ := C.hξ
  have hH := _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ
  have hHeis : IsHeis (fun x y => (star y ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ x).im)
      (rhoVF σ JS JT ξ₀ B.ψ hc ι) := by
    refine ⟨fun f => ?_, fun u v f => ?_, fun u f => norm_rhoBF hc _ f, fun f => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι 0) f = f
      rw [iotaVF_zero, rhoBF_zero]
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) f) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι (u + v)) f
      rw [rhoBF_rhoBF, iotaVF_add, _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι]
    · exact (GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions F E σ nS nT JS JT ξ₀ B.ψ hc f).comp (continuous_iotaVF hι)
  obtain ⟨Ω, ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩, htriv, hcont, hvac⟩ :=
    GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian (IxF F nS nT) (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)) hH.1 hH.2
      (BBF σ JS JT ξ₀ B.ψ) (rhoVF σ JS JT ξ₀ B.ψ hc ι) hHeis (GAF σ JS × GAF σ JT) (mMF σ JS JT θ)
      (_root_.GlobalTheory.T.archimedean_chart_gaussian_vector F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι)
  have sm := _root_.GlobalTheory.T.archimedean_chart_gaussian_norm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc
  have hfr := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀
  have rcomm : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) =
        rhoVF σ JS JT ξ₀ B.ψ hc ι v (rhoBF σ JS JT ξ₀ B.ψ hc u f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, (hfr u _ hu (real_iotaVF hι v)).2, add_comm]
  have radd : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc (u + iotaVF ι v) f = rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, AddChar.map_zero_eq_one, one_smul]
  have hfin : ∀ p {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ f : BBF σ JS JT ξ₀ B.ψ,
      Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) f → Ω p (rhoBF σ JS JT ξ₀ B.ψ hc u f) = rhoBF σ JS JT ξ₀ B.ψ hc u (Ω p f) :=
    fun p u hu f hf => hcomm p _ (fun v g => rcomm hu v g) f hf
  have hth : ∀ p (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 → IsThetaFunOF σ JS JT ξ₀ B.ψ (Ω p f).1 := by
    intro p f hf
    obtain ⟨U, hU, hl⟩ := hf.level
    refine _root_.GlobalTheory.T.archimedean_chart_gaussian_invariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc _ (hsm p f (sm f hf)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoBF σ JS JT ξ₀ B.ψ hc u f = f := QB_ext fun x => congrFun ((coe_rhoBF hc u f).trans (hl u hu h0)) x
    rw [← coe_rhoBF hc, ← hfin p h0 f (sm f hf), e]
  have hbd := GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hc
  obtain ⟨om, hom⟩ := exists_homF hbd Ω hth (fun p f f' h1 h2 => hadd p f f' (sm f h1) (sm f' h2))
    (fun p a f h1 => hsmul p a f (sm f h1)) (fun f h1 => hone f (sm f h1)) fun p p' f h1 => hmul p p' f (sm f h1)
  have lift : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ G : BBF σ JS JT ξ₀ B.ψ, (G.1 : WOF F E nS nT → ℂ) = f :=
    fun f hf => ⟨toBF f hf.cont (hbd f hf) hf.quasi, rfl⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk w f hf => ?_⟩, fun s hs hpos p hsc f hf hv => ?_⟩ <;> obtain ⟨G, rfl⟩ := lift f hf
  · rw [hom p G hf]
    exact hth p G hf
  · simp only [hom _ G hf]
    exact (ev _ _ w).continuous.comp
      (hcont (_root_.GlobalTheory.T.continuous_moment_map F E σ B hB nS nT JS JT θ hθ) G (sm G hf))
  · rw [hom p G hf]
    exact GlobalTheory.T.lintegral_eq_of_heisenbergInvariant_norms F E σ nS nT JS JT ξ₀ B.ψ hc μ 𝓕 hμ h𝓕 _ _
      fun H _ _ _ Φ hΦ => hunit H Φ (fun v g => hΦ _ g) p G (sm G hf)
  · rw [hom _ G hf, htriv _ (mMF_fin θ hg hk) G (sm G hf)]
  · obtain ⟨u, v, hu, rfl⟩ := GlobalTheory.T.exists_finiteAdelic_add_realChartPoint F E nS nT θ ι hι w
    have h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoVF σ JS JT ξ₀ B.ψ hc ι v G).1 :=
      _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀ _ _ hf
    have h2 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v G)).1 :=
      _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀ _ _ h1
    have e1 : actOF σ JS JT g k (u + iotaVF ι v) = u + iotaVF ι (mMF σ JS JT θ (g, k) *ᵥ v) := by
      rw [GlobalTheory.RealWeilF.actOF_add, GlobalTheory.T.unitaryRealPoints_fix_finiteAdelicHoms F E σ nS nT JS JT g k hg hk u hu, _root_.GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι]
    rw [hom _ G hf, e1, ← coe_rhoBF hc _ G, ← coe_rhoBF hc _ (Ω (g, k) G), radd hu v G,
      radd hu _ (Ω (g, k) G), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm G hf)]
  · rw [hom _ G hf, hvac s p hs hpos hsc G (sm G hf) (fderiv_vacF hc ι s G (sm G hf) hv)]
    rfl
end PositivityTheory.ThKW
end
end
