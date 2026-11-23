import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionRightInvariantOpenStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionPreservesCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffRightConvolutionAlongOneParameterProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightDerivativeRightConvolutionEqTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NcardRationalPointsInTranslateLeHeightPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormRightConvolutionLeAdelicHeightPowStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspHS

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Orb

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem norm_convR_le (hP : GlobalTheory.Published.CuspDecayBound) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    ∃ K : ℝ, ∀ F : DividedPowerChartLift V μ, F ∈ L2cusp V μ → ∀ g, ‖convR μ f (lift (GQ V) F) g‖ ≤ K * ‖F‖ := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hfc := continuous_of_mem_ccAd hf
  have hder : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∃ f' ∈ CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : DividedPowerChartLift V μ,
        l.foldr (fun p φ => Rder θ V p.1 p.2 φ) (convR μ f (lift (GQ V) F)) = convR μ f' (lift (GQ V) F) := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨f, hf, subset_rfl, fun F => rfl⟩
    | cons p l ih =>
      intro hl
      obtain ⟨f₁, h₁, s₁, e₁⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      obtain ⟨f₂, h₂, s₂, e₂⟩ := GlobalTheory.T.right_derivative_rightConvolution_eq_test_function μ θ hθ h₁ (hl p List.mem_cons_self)
      exact ⟨f₂, h₂, s₂.trans s₁, fun F => by simp only [List.foldr_cons, e₁ F, e₂ F]⟩
  choose! fl hfl hsl hel using hder
  have hM : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∃ M : ℝ, ∀ y, ‖fl l y‖ ≤ M := fun l hl =>
    have c := continuous_of_mem_ccAd (hfl l hl)
    c.1.bounded_above_of_compact_support c.2
  choose! M hM using hM
  obtain ⟨A, Cg, hg⟩ := GlobalTheory.T.norm_rightConvolution_le_adelic_height_pow μ hfc.2.isCompact (GlobalTheory.T.ncard_rational_points_in_translate_le_height_pow hfc.2.isCompact)
  obtain ⟨U, hU, hlev⟩ := GlobalTheory.T.convolution_right_invariant_open μ hf
  obtain ⟨L, C, hL, hB⟩ := hP D θ hθ V U hU A 0
  refine ⟨C * ∑ l ∈ L, Cg * M l, fun F hF g => ?_⟩
  have hgr : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∀ x,
      ‖(l.foldr (fun p φ => Rder θ V p.1 p.2 φ) (convR μ f (lift (GQ V) F))) x‖ ≤
        Cg * M l * ‖F‖ * GlobalTheory.Grow.height V x ^ A := fun l hl x => by
    rw [hel l hl F]
    exact hg _ (continuous_of_mem_ccAd (hfl l hl)).1 (hsl l hl) _ (hM l hl) F x
  have hcont := (GlobalTheory.AutomorphicL2Local.continuous_convR_lift _ (GQ V) μ f hfc.1 hfc.2 F).2
  have key := hB (convR μ f (lift (GQ V) F))
    ⟨fun γ hγ x => ((leftInv_lift (Γ := GQ V) F).convR (μ := μ) f) γ hγ x, ⟨U, hU, hlev F⟩, hcont⟩
    (hlev F) (GlobalTheory.T.contDiff_rightConvolution_along_one_parameter_products μ θ hθ hf F) (fun l hl => ⟨_, hgr l hl⟩) (GlobalTheory.T.convolution_preserves_cuspidal μ hf F hF)
    (fun l => Cg * M l * ‖F‖) (fun l hl x => hgr l (hL l hl) x) g
  rw [pow_zero, mul_one, ← Finset.sum_mul, ← mul_assoc] at key
  exact key

theorem isHilbertSchmidt_RcuspOp (hP : GlobalTheory.Published.CuspDecayBound) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    IsHilbertSchmidt (RcuspOp V μ f) := by
  obtain ⟨K, hK⟩ := norm_convR_le (μ := μ) hP hf
  have hfc := continuous_of_mem_ccAd hf
  have hi : Integrable f μ := hfc.1.integrable_of_hasCompactSupport hfc.2
  have h1 : IsHilbertSchmidt ((L2cusp V μ).subtypeL ∘L RcuspOp V μ f) := by
    refine GlobalTheory.T.isHilbertSchmidt_of_ae_pointwise_bounded_Lp_two _ K fun v => ?_
    have e : ((L2cusp V μ).subtypeL ∘L RcuspOp V μ f) v = RopG V μ f v := coe_RcuspOp V μ hi v
    rw [e]
    refine ae_quotMeasure_iff.2 ?_
    filter_upwards [(GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f hi v).2] with x hx
    have hx' : (RopG V μ f v) (mk (GQ V) x) = convR μ f (lift (GQ V) (v : DividedPowerChartLift V μ)) x := hx
    rw [hx']
    simpa using hK v v.2 x
  exact h1.of_norm_le 1 fun x => by simp

end GlobalTheory.CuspHS

namespace GlobalTheory.Published

theorem cuspTraceClass_of_decay (hP : CuspDecayBound) (hDM : DixmierMalliavinFactorisation) : CuspTraceClass :=
  fun _ _ _ _ _ _ hf => CuspSpectrum.isTraceClass_of_isHilbertSchmidt hDM
    (fun _ hg => CuspHS.isHilbertSchmidt_RcuspOp hP hg) hf

end GlobalTheory.Published

end
