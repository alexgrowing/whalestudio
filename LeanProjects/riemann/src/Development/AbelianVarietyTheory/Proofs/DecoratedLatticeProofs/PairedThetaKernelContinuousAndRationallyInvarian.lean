import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.PairKer

variable {D : D7}

noncomputable def mulRight (S : HSp D) (m : ℕ) (γ : GA D S) : Mx D m S.rank ≃+ Mx D m S.rank where
  toFun w := w ⬝ mt S γ
  invFun w := w ⬝ mt S γ⁻¹
  left_inv w := by simp only [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  right_inv w := by simp only [Matrix.mul_assoc, mt_inv_mul, Matrix.mul_one]
  map_add' x y := Matrix.add_mul _ _ _

theorem om_emb {ψ : AddChar (AF D.host.F) ℂ} {S T A L : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T}
    (h : IsWeilDatumO ψ S T χ χ' om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (o : OrthDec T A L) {γ : GA D A}
    (hγ : γ ∈ GQ A) (h₀ : GA D S) (h₁ : GA D A) (w : WO S L) :
    om (h₀, o.emb (γ * h₁, 1)) f (o.jB ⬝ w) = om (h₀, o.emb (h₁, 1)) f (o.jB ⬝ w) := by
  have hg : o.emb (γ, 1) ∈ GQ T := o.emb_mem_GQ hγ (GQ L).one_mem
  have a1 : o.emb (γ, 1) * o.emb (h₁, 1) = o.emb (γ * h₁, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have a2 : (o.emb (γ, 1))⁻¹ = o.emb (γ⁻¹, 1) := by
    rw [← map_inv]; exact congrArg _ (Prod.ext rfl inv_one)
  have a3 : mt T (o.emb (γ⁻¹, 1)) ⬝ (o.jB ⬝ w) = o.jB ⬝ w := by
    rw [cancel₂ (o.emb_jB _ _), mt_one, Matrix.mul_one]
  have key : ∀ (δ : GA D T) (x : WO S T), δ ∈ GQ T → mt T δ⁻¹ ⬝ x = x → ∀ k, om (h₀, δ * k) f x = om (h₀, k) f x := by
    intro δ x hδ hx k
    have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ S T _ _ _ h f hf 1 (GQ S).one_mem δ hδ h₀ k x
    rwa [one_mul h₀, hx, mt_one, Matrix.mul_one] at e
  rw [← a1]
  exact key _ _ hg (by rw [a2]; exact a3) _

theorem pairKer_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W₀ B.V₀ Ξ → Continuous (Function.uncurry (pairKer s vL Y Ξ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, pairKer s vL Y Ξ (γ * h₀) h₁ = pairKer s vL Y Ξ h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, pairKer s vL Y Ξ h₀ (γ * h₁) = pairKer s vL Y Ξ h₀ h₁ := by
  intro D ψ σ J B s vL Y Ξ hY hΞ
  have hn : ∀ x, ψ x * star (ψ x) = 1 := fun x => by
    have h1 : ‖ψ x‖ = 1 := s.weil₀.std.1.2.1 x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  set K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.A → ℂ := fun w p =>
    s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ w) * star (Y p.1 w) with hK
  have hP : ∀ h₀ h₁, pairKer s vL Y Ξ h₀ h₁ = ∫ w in vL.𝓕, K w (h₀, h₁) ∂vL.μ := fun h₀ h₁ => by
    simp only [pairKer, contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ _ _ _ s.weil₀ Ξ hΞ
    have h2 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        (((q.2.1, B.o.emb (q.2.2, 1)), B.o.jB ⬝ q.1) : (GA D J.W₀ × GA D B.V₀) × WO J.W₀ B.V₀) :=
      ((continuous_fst.comp continuous_snd).prodMk (B.o.continuous_emb.comp
        ((continuous_snd.comp continuous_snd).prodMk continuous_const))).prodMk
        (continuous_const.matrix_mul continuous_fst)
    have h3 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        ((q.2.1, q.1) : GA D J.W₀ × WO J.W₀ B.L) := (continuous_fst.comp continuous_snd).prodMk continuous_fst
    exact (h1.comp h2).mul (hY.cont.comp h3).star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ x p, K (γ + x) p = K x p := by
    rintro _ ⟨γ, rfl⟩ x p
    have e1 := (s.weil₀.om_pres (p.1, B.o.emb (p.2, 1)) Ξ hΞ).quasi (B.o.iB * γ) (B.o.jB ⬝ x)
    have e2 := hY.quasi p.1 γ x
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ x) = symplOH J.W₀ B.L (rat γ) x := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ (rat γ + x)) * star (Y p.1 (rat γ + x)) =
      s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ x) * star (Y p.1 x)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ x)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, hcont, -, hinv⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D _ _ vL _ K hc hper
  refine ⟨?_, fun γ hγ h₀ h₁ => ?_, fun γ hγ h₀ h₁ => ?_⟩
  · have : Function.uncurry (pairKer s vL Y Ξ) = fun p => ∫ w in vL.𝓕, K w p ∂vL.μ := funext fun p => hP p.1 p.2
    rw [this]; exact hcont
  · rw [hP, hP, ← hinv (mulRight J.W₀ _ γ) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const) ?_ (h₀, h₁)]
    · congr 1; funext w
      have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ s.weil₀ Ξ hΞ γ hγ 1 (one_mem _) h₀ (B.o.emb (h₁, 1)) (B.o.jB ⬝ w)
      rw [one_mul, inv_one, mt_one, Matrix.one_mul, Matrix.mul_assoc] at e
      change s.om₀ (γ * h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ w) * star (Y (γ * h₀) w) =
        s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ (w ⬝ mt J.W₀ γ)) * star (Y h₀ (w ⬝ mt J.W₀ γ))
      rw [e, hY.left γ hγ]
    · intro x
      refine ⟨fun h => ?_, fun h => ratMx_mul h ((mem_GQ_iff _ _).1 hγ)⟩
      rw [← (mulRight J.W₀ _ γ).symm_apply_apply x]
      exact ratMx_mul h ((mem_GQ_iff _ _).1 (inv_mem hγ))
  · rw [hP, hP]
    congr 1; funext w
    have e := om_emb s.weil₀ hΞ B.o hγ h₀ h₁ w
    change s.om₀ (h₀, B.o.emb (γ * h₁, 1)) Ξ (B.o.jB ⬝ w) * star (Y h₀ w) =
      s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ w) * star (Y h₀ w)
    rw [e]

end GlobalTheory.PairKer
