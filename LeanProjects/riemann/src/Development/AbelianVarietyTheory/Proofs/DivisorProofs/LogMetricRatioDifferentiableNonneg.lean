import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMetricDerivativeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarLocalChartEstimateStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HodgeGradNear

theorem abs_fderiv_lnRatio_le_near : Hypotheses2 → HypothesesH → OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ρ : DV.Rt D.what₂.Tau O.N)
  (y₀ : GlobalTheory.CxPts (O.var c).str σ), y₀ ∉ offBd O.Φ c σ →
  ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (C μ : ℝ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ ch.e.source ∧ 0 ≤ μ ∧ ∀ y ∈ U, y ∈ offBd O.Φ c σ →
      DifferentiableAt ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ∧
      ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim,
        |fderiv ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ξ| ≤
          C * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) := by
  intro h2 hH D O x P hC hf hR c σ ρ y₀ hy₀
  obtain ⟨ch, U, Hh, H0, μ, K, c₀, C₀, hU, hy₀U, hUs, hUo, hc₀, hμ, hB⟩ := GlobalTheory.T.l2_dbar_local_chart_estimate h2 hH D O x P hC hf hR c σ y₀ hy₀
  set S := ch.e '' (U ∩ offBd O.Φ c σ) with hS
  have hSo : IsOpen S := ch.e.isOpen_image_of_subset_source hUo (Set.inter_subset_left.trans hUs)
  have hmemS : ∀ w ∈ S, ch.e.symm w ∈ U ∧ ch.e.symm w ∈ offBd O.Φ c σ ∧ ch.e (ch.e.symm w) = w := by
    rintro w ⟨y, ⟨hyU, hyo⟩, rfl⟩
    rw [ch.e.left_inv (hUs hyU)]
    exact ⟨hyU, hyo, rfl⟩
  have hr1 : ∀ y, 1 ≤ O.met.r c σ y := fun y => by
    rw [hC.r_eq]
    exact le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) exp_le_rFlag
  have hA : ∀ τ : D.host.E →+* ℂ, ∃ K' : ℝ, 0 ≤ K' ∧ ∀ w ∈ S, ∀ i : Fin (O.S.Dw.mult τ),
      DifferentiableAt ℝ (fun w' => Real.log (grSq (Hh τ w') i) - Real.log (grSq (H0 τ w') i)) w ∧
      ∀ ξ, |fderiv ℝ (fun w' => Real.log (grSq (Hh τ w') i) - Real.log (grSq (H0 τ w') i)) w ξ| ≤
        K' * O.met.r c σ (ch.e.symm w) ^ (3 * μ) * Real.exp (O.met.r c σ (ch.e.symm w) / 2) *
          √(P.om c σ ch (ch.e.symm w) ξ.ofLp) := by
    intro τ
    refine GlobalTheory.T.hermitian_metric_derivative_bound _ S (Hh τ) (H0 τ) (fun w => O.met.r c σ (ch.e.symm w))
      (fun w ξ => √(P.om c σ ch (ch.e.symm w) ξ.ofLp)) μ K c₀ C₀ hSo hc₀ hμ ?_ ?_ ?_
    · intro w hw
      obtain ⟨h1, h2, h3⟩ := hmemS w hw
      have e := (hB _ h1 h2).2 τ
      rw [h3] at e
      exact ⟨hr1 _, e.1, e.2.1, e.2.2.1⟩
    · intro w hw v
      obtain ⟨h1, h2, h3⟩ := hmemS w hw
      have e := (hB _ h1 h2).2 τ
      rw [h3] at e
      exact e.2.2.2.1 v
    · intro w hw ξ
      obtain ⟨h1, h2, h3⟩ := hmemS w hw
      have e := (hB _ h1 h2).2 τ
      rw [h3] at e
      exact e.2.2.2.2 ξ
  choose K' hK'0 hK' using hA
  refine ⟨ch, U, (∑ z : Letter O.S.Dw, |(O.ex ρ z : ℝ)|) / 2 * ∑ τ, K' τ, 3 * μ, hU, hy₀U, hUs, by positivity,
    fun y hyU hyo => ?_⟩
  have hwS : ch.e y ∈ S := ⟨y, ⟨hyU, hyo⟩, rfl⟩
  have hy' : ch.e.symm (ch.e y) = y := ch.e.left_inv (hUs hyU)
  set g : Letter O.S.Dw → ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → ℝ :=
    fun z w' => Real.log (grSq (Hh z.1 w') z.2) - Real.log (grSq (H0 z.1 w') z.2) with hg
  set F : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → ℝ := fun w' => (∑ z : Letter O.S.Dw, (O.ex ρ z : ℝ) * g z w') / 2 with hF
  have hEq : (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) =ᶠ[nhds (ch.e y)] F := by
    filter_upwards [hSo.mem_nhds hwS] with w' hw'
    obtain ⟨h1, h2, h3⟩ := hmemS w' hw'
    have e := (hB _ h1 h2).1 (O.ex ρ)
    rw [h3] at e
    exact e
  have hgd : ∀ z : Letter O.S.Dw, HasFDerivAt (g z) (fderiv ℝ (g z) (ch.e y)) (ch.e y) := fun z =>
    ((hK' z.1 _ hwS z.2).1).hasFDerivAt
  have hFd : HasFDerivAt F ((1 / 2 : ℝ) • ∑ z : Letter O.S.Dw, (O.ex ρ z : ℝ) • fderiv ℝ (g z) (ch.e y)) (ch.e y) := by
    have hs : HasFDerivAt (fun w' => ∑ z ∈ Finset.univ, (O.ex ρ z : ℝ) * g z w')
        (∑ z ∈ Finset.univ, (O.ex ρ z : ℝ) • fderiv ℝ (g z) (ch.e y)) (ch.e y) :=
      HasFDerivAt.fun_sum fun z _ => (hgd z).const_mul (O.ex ρ z : ℝ)
    refine (hs.const_mul (1 / 2 : ℝ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w' => ?_)
    simp only [hF]
    ring
  have hFd' := hFd.congr_of_eventuallyEq hEq
  refine ⟨hFd'.differentiableAt, fun ξ => ?_⟩
  rw [hFd'.fderiv]
  set R := O.met.r c σ y ^ (3 * μ) * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) with hR
  have hR0 : 0 ≤ R := by
    have := Real.rpow_nonneg (zero_le_one.trans (hr1 y)) (3 * μ)
    positivity
  have hz : ∀ z : Letter O.S.Dw, |fderiv ℝ (g z) (ch.e y) ξ| ≤ (∑ τ, K' τ) * R := fun z => by
    have e := (hK' z.1 _ hwS z.2).2 ξ
    rw [hy'] at e
    have hle : K' z.1 ≤ ∑ τ, K' τ := Finset.single_le_sum (fun τ _ => hK'0 τ) (Finset.mem_univ _)
    calc |fderiv ℝ (g z) (ch.e y) ξ| ≤ K' z.1 * R := by rw [hR]; linarith [e]
      _ ≤ (∑ τ, K' τ) * R := mul_le_mul_of_nonneg_right hle hR0
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hs : |∑ z : Letter O.S.Dw, (O.ex ρ z : ℝ) * fderiv ℝ (g z) (ch.e y) ξ| ≤
      ∑ z : Letter O.S.Dw, |(O.ex ρ z : ℝ)| * ((∑ τ, K' τ) * R) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hz z) (abs_nonneg _)
  rw [← Finset.sum_mul] at hs
  have : (1 / 2 : ℝ) * |∑ z : Letter O.S.Dw, (O.ex ρ z : ℝ) * fderiv ℝ (g z) (ch.e y) ξ| ≤
      (1 / 2) * ((∑ z : Letter O.S.Dw, |(O.ex ρ z : ℝ)|) * ((∑ τ, K' τ) * R)) :=
    mul_le_mul_of_nonneg_left hs (by norm_num)
  calc _ ≤ _ := this
    _ = _ := by rw [hR]; ring

end GlobalTheory.HodgeGradNear
