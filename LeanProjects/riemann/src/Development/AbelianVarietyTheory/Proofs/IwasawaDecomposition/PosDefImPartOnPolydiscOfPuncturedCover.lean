import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem posDef_im_on_ball_of_logExp : ∀ (n a : ℕ) (J : Type) [Fintype J] [DecidableEq J] (Δ : (Fin n → ℂ) → Matrix J J ℂ), (∀ i j, DifferentiableOn ℂ (fun z => Δ z i j) (Metric.ball 0 1)) → (∀ s ∈ logDom n a, ((Δ (logExp a s)).map Complex.im).PosDef) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ((Δ z).map Complex.im).PosDef := by
  intro n a J _ _ Δ hΔ hpos z hz
  set U := Metric.ball (0 : Fin n → ℂ) 1 with hU
  have hcont : ∀ i j, ContinuousOn (fun w => Δ w i j) U := fun i j => (hΔ i j).continuousOn
  have hM : ContinuousOn (fun w => (Δ w).map Complex.im) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont i j)
  have hMT : ContinuousOn (fun w => ((Δ w).map Complex.im)ᵀ) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont j i)
  have hsymm : ((Δ z).map Complex.im)ᵀ = (Δ z).map Complex.im := by
    refine eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix J J ℝ)
      (fun w => ((Δ w).map Complex.im)ᵀ) (fun w => (Δ w).map Complex.im) le_rfl hMT hM ?_ z hz
    intro s hs _
    have h1 := (hpos s hs).1
    unfold Matrix.IsHermitian at h1
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  intro x hx
  set q : (Fin n → ℂ) → ℂ := fun w => ∑ i, ∑ j, (x i : ℂ) * Δ w i j * (x j : ℂ) with hq
  have hqim : ∀ w, (q w).im = star x ⬝ᵥ ((Δ w).map Complex.im *ᵥ x) := by
    intro w
    simp [q, dotProduct, mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum, mul_comm,
      mul_left_comm, mul_assoc]
  have hqd : DifferentiableOn ℂ q U := by
    rw [hq]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.fun_sum
    intro j _
    exact ((hΔ i j).const_mul (x i : ℂ)).mul_const (x j : ℂ)
  have hqpos : ∀ s ∈ logDom n a, 0 < (q (logExp a s)).im := by
    intro s hs
    rw [hqim]
    exact (hpos s hs).dotProduct_mulVec_pos hx
  have hqc : ContinuousOn (fun w => (q w).im) U :=
    Complex.continuous_im.comp_continuousOn hqd.continuousOn
  have hnn : ∀ w ∈ U, 0 ≤ (q w).im := by
    intro w hw
    have := eq_on_ball_of_eq_on_logExp_image n a 1 ℝ (fun w => min (q w).im 0) (fun _ => 0)
      le_rfl ((continuous_id.min continuous_const).comp_continuousOn hqc) continuousOn_const
      (fun s hs _ => min_eq_right (hqpos s hs).le) w hw
    exact (min_eq_right_iff.1 this)
  rw [← hqim]
  rcases (hnn z hz).lt_or_eq with h | h0
  · exact h
  exfalso
  set F : (Fin n → ℂ) → ℂ := fun w => Complex.exp (Complex.I * q w) with hF
  have hFn : ∀ w, ‖F w‖ = Real.exp (-(q w).im) := by
    intro w
    simp [F, Complex.norm_exp, Complex.I_mul_re]
  have hFd : DifferentiableOn ℂ F U := (hqd.const_mul Complex.I).cexp
  have hmax : IsMaxOn (norm ∘ F) U z := by
    intro w hw
    simp only [Set.mem_setOf_eq, Function.comp, hFn, ← h0, neg_zero]
    exact Real.exp_le_exp.2 (by linarith [hnn w hw])
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : Fin n → ℂ) 1).isPreconnected
    Metric.isOpen_ball hFd hz hmax
  obtain ⟨s, hs⟩ := (GlobalTheory.ShFam.Hor.Mark.nonempty_logDom : (logDom n a).Nonempty)
  have hmem : logExp a s ∈ U := GlobalTheory.ShFam.Hor.Mark.logExp_mem hs
  have h2 := congrArg norm (heq hmem)
  simp only [Function.const_apply, hFn, ← h0, neg_zero] at h2
  have h3 : (q (logExp a s)).im = 0 := by
    have := Real.exp_injective h2
    linarith
  exact (hqpos s hs).ne' h3

end GlobalTheory
