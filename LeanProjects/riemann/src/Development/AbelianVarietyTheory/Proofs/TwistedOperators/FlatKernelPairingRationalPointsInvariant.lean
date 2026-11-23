import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.XLastLin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerRat

theorem flat_kernel_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ ((γ * h₀), B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz ((γ * h₀), 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb ((γ * h₁), 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ h
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  have hΞ : IsThetaFunO ψ J.W₀ B.V₀ (flFB s (s.om (1, h) Φ)) := by
    have e := (GlobalTheory.Unf.Flat.flatLaw D ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU x hx 0
      (s.om (1, h) Φ) (s.weil.om_pres (1, h) Φ hΦ)).2
    simp only [flFB, flatS, hxe]
    exact e
  generalize flFB s (s.om (1, h) Φ) = Ξ at hΞ ⊢
  set Y : GA D J.W₀ → WO J.W₀ B.L → ℂ := fun h₀ => omz (h₀, 1) Φ₀ with hYdef
  have hYl : ∀ γ ∈ GQ J.W₀, ∀ h₀ w, Y (γ * h₀) w = Y h₀ (w ⬝ mt J.W₀ γ) := by
    intro γ hγ h₀ w
    have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ J.W₀ B.L χ χz omz homz Φ₀ hΦ₀ γ hγ 1 (one_mem _) h₀ 1 w
    rw [one_mul, inv_one, mt_one, Matrix.one_mul] at e
    exact e
  have hJ : Continuous fun p : (GA D J.W₀ × GA D B.L) × WO J.W₀ B.L => omz p.1 Φ₀ p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ _ _ χ χz omz homz Φ₀ hΦ₀
  have hYc : Continuous fun p : GA D J.W₀ × WO J.W₀ B.L => Y p.1 p.2 :=
    hJ.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
  have hn : ∀ x, ψ x * star (ψ x) = 1 := fun x => by
    have h1 : ‖ψ x‖ = 1 := s.weil₀.std.1.2.1 x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  set K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.A → ℂ := fun w p =>
    s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ w) * star (Y p.1 w) with hK
  have hP : ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ) (omz (h₀, 1) Φ₀) 0 =
      ∫ w in vL.𝓕, K w (h₀, h₁) ∂vL.μ := fun h₀ h₁ => by
    simp only [contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK, hYdef]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ _ _ _ s.weil₀ Ξ hΞ
    have h2 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        (((q.2.1, B.o.emb (q.2.2, 1)), B.o.jB ⬝ q.1) : (GA D J.W₀ × GA D B.V₀) × WO J.W₀ B.V₀) :=
      ((continuous_fst.comp continuous_snd).prodMk (B.o.continuous_emb.comp
        ((continuous_snd.comp continuous_snd).prodMk continuous_const))).prodMk
        (continuous_const.matrix_mul continuous_fst)
    have h3 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        ((q.2.1, q.1) : GA D J.W₀ × WO J.W₀ B.L) := (continuous_fst.comp continuous_snd).prodMk continuous_fst
    exact (h1.comp h2).mul (hYc.comp h3).star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ x p, K (γ + x) p = K x p := by
    rintro _ ⟨γ, rfl⟩ x p
    have e1 := (s.weil₀.om_pres (p.1, B.o.emb (p.2, 1)) Ξ hΞ).quasi (B.o.iB * γ) (B.o.jB ⬝ x)
    have e2 := (homz.om_pres (p.1, 1) Φ₀ hΦ₀).quasi γ x
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ x) = symplOH J.W₀ B.L (rat γ) x := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ (rat γ + x)) * star (omz (p.1, 1) Φ₀ (rat γ + x)) =
      s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ x) * star (omz (p.1, 1) Φ₀ x)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ x)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, -, -, hinv⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D _ _ vL _ K hc hper
  refine ⟨fun γ hγ h₀ h₁ => ?_, fun γ hγ h₀ h₁ => ?_⟩
  · rw [hP, hP, ← hinv (GlobalTheory.PairKer.mulRight J.W₀ _ γ) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const) ?_ (h₀, h₁)]
    · congr 1; funext w
      have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ s.weil₀ Ξ hΞ γ hγ 1 (one_mem _) h₀ (B.o.emb (h₁, 1)) (B.o.jB ⬝ w)
      rw [one_mul, inv_one, mt_one, Matrix.one_mul, Matrix.mul_assoc] at e
      change s.om₀ (γ * h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ w) * star (Y (γ * h₀) w) =
        s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ (w ⬝ mt J.W₀ γ)) * star (Y h₀ (w ⬝ mt J.W₀ γ))
      rw [e, hYl γ hγ]
    · intro x
      refine ⟨fun h => ?_, fun h => ratMx_mul h ((mem_GQ_iff _ _).1 hγ)⟩
      rw [← (GlobalTheory.PairKer.mulRight J.W₀ _ γ).symm_apply_apply x]
      exact ratMx_mul h ((mem_GQ_iff _ _).1 (inv_mem hγ))
  · refine (hP h₀ (γ * h₁)).trans (Eq.trans ?_ (hP h₀ h₁).symm)
    refine integral_congr_ae (.of_forall fun w => ?_)
    have e := GlobalTheory.PairKer.om_emb s.weil₀ hΞ B.o hγ h₀ h₁ w
    show K w (h₀, γ * h₁) = K w (h₀, h₁)
    rw [hK]
    exact congrArg (· * star (Y h₀ w)) e

end GlobalTheory.KerRat

end
