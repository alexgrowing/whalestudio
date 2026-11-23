import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChartStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtLogH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}

open MvPolynomial in
theorem coneTangent_inv (hP : IsMultiHomogIdeal P) {z w : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) (hw : IsConeTangent (Int.castRingHom ℂ) P (torusSmul c z) w) :
    IsConeTangent (Int.castRingHom ℂ) P z (torusSmul c⁻¹ w) := by
  obtain ⟨S, hS, hPS⟩ := hP
  have hle : Ideal.span S ≤ (tanIdeal z (torusSmul c⁻¹ w)).comap (MvPolynomial.map (Int.castRingHom ℂ)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨d, hd⟩ := hS f hf
    have hfP : f ∈ P := by rw [hPS]; exact Ideal.subset_span hf
    refine mem_tanIdeal.2 ⟨hz.2 f hfP, ?_⟩
    have hd' : ReciprocityTheory.AnForm.R.IsMultiHomog (MvPolynomial.map (Int.castRingHom ℂ) f) d :=
      fun m hm k => hd m (support_map_subset _ _ hm) k
    have hne : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
    apply mul_left_cancel₀ hne
    rw [mul_zero, Finset.mul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) (hw f hfP)
    rw [← _root_.mul_assoc, ← eval_pderiv_scale hd' c z q]
    have := hc q.1
    show c q.1 * eval (torusSmul c z) (pderiv q (MvPolynomial.map (Int.castRingHom ℂ) f)) * ((c q.1)⁻¹ * w q) = _
    field_simp
  intro f hf
  rw [hPS] at hf
  exact (mem_tanIdeal.1 (hle hf)).2

theorem levi_of_chart {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {A : HermLine J}
    (hA : IsSmoothHerm A) {t u : Fin n → ℂ} (ht : t ∈ Metric.ball (0 : Fin n → ℂ) 1) {c c' : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {w : (Σ k, J k) → ℂ}
    (hw : torusSmul c⁻¹ w = fderiv ℂ χ.γ t u + torusSmul c' (χ.γ t)) :
    levi (fun z => Real.log (A.h z)) (torusSmul c (χ.γ t)) w = levi (fun t' => Real.log (A.h (χ.γ t'))) t u := by
  have hγ := χ.analytic t ht
  have hz := (χ.mem t ht).1
  have hℓa : AnalyticAt ℂ (fun ζ : ℂ => t + ζ • u) 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hℓ0 : t + (0 : ℂ) • u = t := by simp
  have hℓd : HasDerivAt (fun ζ : ℂ => t + ζ • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add t
  have hγ' : AnalyticAt ℂ χ.γ (t + (0 : ℂ) • u) := by rw [hℓ0]; exact hγ
  have hga : AnalyticAt ℂ (fun ζ : ℂ => χ.γ (t + ζ • u)) 0 :=
    AnalyticAt.comp (g := χ.γ) (f := fun ζ : ℂ => t + ζ • u) hγ' hℓa
  have hgd : HasDerivAt (fun ζ : ℂ => χ.γ (t + ζ • u)) (fderiv ℂ χ.γ t u) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hγ.differentiableAt.hasFDerivAt hℓd hℓ0.symm
  have hψ : ContDiffAt ℝ 2 (fun t' => Real.log (A.h (χ.γ t'))) t := by
    have hR : AnalyticAt ℝ χ.γ t := hγ.restrictScalars
    exact ContDiffAt.comp (g := fun z => Real.log (A.h z)) t (contDiffAt_log_h hA hz) hR.contDiffAt
  let δ : ℂ → (Σ k, J k) → ℂ := fun ζ => torusSmul (fun k => c k * Complex.exp (ζ * c' k)) (χ.γ (t + ζ • u))
  have hδa : AnalyticAt ℂ δ 0 := analyticAt_pi_iff.2 fun p =>
    (analyticAt_const.mul (analyticAt_id.mul analyticAt_const).cexp).mul (analyticAt_pi_iff.1 hga p)
  have hδ0 : δ 0 = torusSmul c (χ.γ t) := by
    funext p
    simp [δ, torusSmul]
  have hδd : HasDerivAt δ w 0 := by
    refine hasDerivAt_pi.2 fun p => ?_
    have h1 := (((hasDerivAt_id (0 : ℂ)).mul_const (c' p.1)).cexp.const_mul (c p.1)).mul (hasDerivAt_pi.1 hgd p)
    have h2 : (c p.1)⁻¹ * w p = fderiv ℂ χ.γ t u p + c' p.1 * χ.γ t p := congrFun hw p
    have h3 : w p = c p.1 * (fderiv ℂ χ.γ t u p + c' p.1 * χ.γ t p) := by
      rw [← h2, mul_inv_cancel_left₀ (hc p.1)]
    refine HasDerivAt.congr_deriv h1 ?_
    rw [h3]
    simp
    ring
  have hcz : ∀ k, ∃ i, torusSmul c (χ.γ t) ⟨k, i⟩ ≠ 0 := fun k => (hz k).imp fun i hi => mul_ne_zero (hc k) hi
  rw [levi_disc hδa hδd hδ0 (contDiffAt_log_h hA hcz), levi_disc hℓa hℓd hℓ0 hψ]
  have hp : AnalyticAt ℂ (fun s : Fin 1 → ℂ => s 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0
  have hq : AnalyticAt ℂ (fun s : Fin 1 → ℂ => t + s 0 • u) 0 := analyticAt_const.add (hp.smul analyticAt_const)
  have hq0 : t + (0 : Fin 1 → ℂ) 0 • u = t := by simp
  refine levi_add_re (G := fun s => ∑ k, (A.a k : ℂ) * ((Real.log ‖c k‖ : ℝ) + s 0 * c' k)) ?_
    (Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul (analyticAt_const.add (hp.mul analyticAt_const))) ?_ _
  · have hR : AnalyticAt ℝ (fun s : Fin 1 → ℂ => t + s 0 • u) 0 := hq.restrictScalars
    exact ContDiffAt.comp (g := fun t' => Real.log (A.h (χ.γ t'))) (f := fun s : Fin 1 → ℂ => t + s 0 • u) 0
      (by rw [hq0]; exact hψ) hR.contDiffAt
  · have hq1 : t + (0 : Fin 1 → ℂ) 0 • u ∈ Metric.ball (0 : Fin n → ℂ) 1 := by rw [hq0]; exact ht
    filter_upwards [hq.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hq1)] with s hs
    rw [show δ (s 0) = torusSmul (fun k => c k * Complex.exp (s 0 * c' k)) (χ.γ (t + s 0 • u)) from rfl,
      log_h_smul A (χ.mem _ hs).1 fun k => mul_ne_zero (hc k) (Complex.exp_ne_zero _), Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)),
      Complex.norm_exp, Real.log_exp, ← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.add_re,
      Complex.ofReal_re]

end

theorem levi_nonneg_semipositive_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (A : HermLine J), IsSmoothHerm A → (∀ a, ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, 0 ≤ levi (fun t' => Real.log (A.h ((D.chart a).γ t'))) t v) → IsSemipositiveH (mCoordIdeal D.y) A := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D A hA h
  refine ⟨hA, fun z hz w hw => ?_⟩
  obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z hz
  have ht' : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
    mem_ball_zero_iff.2 (ht.trans_lt (by norm_num))
  obtain ⟨u, c', hu⟩ := GlobalTheory.T.cone_tangent_lift_in_chart K J II Ψ Ω W D a t ht' _
    (coneTangent_inv D.arith.2.1.2.1 ((D.chart a).mem t ht') hc hw)
  exact (h a t ht u).trans_eq (levi_of_chart (D.chart a) hA ht' hc hu).symm

end LevelTowerAlt
