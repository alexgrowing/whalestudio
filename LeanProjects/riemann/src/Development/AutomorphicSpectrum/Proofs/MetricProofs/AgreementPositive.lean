import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereRegularizationLogLogBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionDifferenceTelescopingIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TendstoLimUnderOfCauchyRate
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LimRateMulLogSqLe
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbsCoeffProdXLeOne

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

def agreeRate (t : ℝ) : ℝ := Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)

theorem agree_exp_le_sq {s : ℝ} (hs : 0 < s) : Real.exp (-(s ^ 2)⁻¹) ≤ s ^ 2 := by
  have hx : 0 < (s ^ 2)⁻¹ := by positivity
  have h1 : (s ^ 2)⁻¹ ≤ Real.exp ((s ^ 2)⁻¹) := by linarith [Real.add_one_le_exp ((s ^ 2)⁻¹)]
  rw [Real.exp_neg]
  calc (Real.exp (s ^ 2)⁻¹)⁻¹ ≤ ((s ^ 2)⁻¹)⁻¹ := inv_anti₀ hx h1
    _ = s ^ 2 := inv_inv _

theorem agreeRate_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ agreeRate (Real.exp (-(s ^ 2)⁻¹)) := by
  unfold agreeRate
  rw [limRate_log_inv_exp]
  have : 0 < (s ^ 2)⁻¹ := by positivity
  positivity

theorem agree_cauchy (hI : Inputs) (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (h0 : 0 < S.t₀) :
    ∃ C' t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ S.t₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P)
      (w : Fin (D + 1) → σ) (t t' : ℝ), 0 < t' → t' ≤ t → t ≤ t₁ →
      |Re.num II t w - Re.num II t' w| ≤ ((D : ℝ) + 1) * (|C'| * |agreeRate t|) := by
  obtain ⟨C', t₁, ht₁, ht₁0, hb⟩ := GlobalTheory.T.monge_ampere_regularization_log_log_bound hI.convergenceRate D σ S h0
  refine ⟨C', t₁, ht₁, ht₁0, ?_⟩
  intro II hII K _ ι _ P Re w t t' ht' htt ht
  have ht0 : 0 < t := lt_of_lt_of_le ht' htt
  rw [GlobalTheory.T.intersection_difference_telescoping_integral hI II hII K ι D σ S P Re t t' w ht0 (ht.trans ht₁0) ht' ((htt.trans ht).trans ht₁0)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hr : ∀ r : Fin (D + 1), |mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t'))
      (fun x => S.phT (w r) t x - S.phT (w r) t' x)| ≤ |C'| * |agreeRate t| := by
    intro r
    have := hb t t' ht' htt ht (w r) (fun i => w (r.succAbove i)) (fun i => decide (r.succAbove i < r))
    simp only [decide_eq_true_eq] at this
    refine this.trans ?_
    rw [mul_div_assoc]
    exact (le_abs_self _).trans (by rw [abs_mul]; rfl)
  refine (Finset.sum_le_sum fun r _ => hr r).trans ?_
  simp

theorem agreementPos : AgreementPos := by
  intro hI D σ _ S abelian₂ h0
  obtain ⟨C', t₁, ht₁, ht₁0, hc⟩ := agree_cauchy hI D σ S h0
  obtain ⟨hlim, hrate, -, -⟩ := limRate
  refine ⟨|abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * 4)), min 1 t₁, lt_min one_pos ht₁, ?_⟩
  intro II hII K _ ι _ P Re
  have hδ : Tendsto (fun t => ((D : ℝ) + 1) * (|C'| * |agreeRate t|)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t => |agreeRate t|) (𝓝[>] 0) (𝓝 0) := by
      have h2 := hlim.abs
      rw [abs_zero] at h2
      exact h2
    simpa using (this.const_mul |C'|).const_mul ((D : ℝ) + 1)
  have hL := fun w => tendsto_limUnder_of_cauchy_rate (fun t => Re.num II t w)
    (fun t => ((D : ℝ) + 1) * (|C'| * |agreeRate t|)) t₁ ht₁ hδ (hc II hII K ι P Re w)
  refine ⟨fun w => (hL w).1, fun s hs hss => ?_⟩
  have hs1 : s ≤ 1 := hss.trans (min_le_left _ _)
  have hst : s ≤ t₁ := hss.trans (min_le_right _ _)
  have hT : Real.exp (-(s ^ 2)⁻¹) ≤ t₁ := by
    refine (agree_exp_le_sq hs).trans ?_
    nlinarith
  refine ⟨hT.trans ht₁0, fun c hcL => ?_⟩
  set t := Real.exp (-(s ^ 2)⁻¹)
  have hM : ∀ w, |Re.num II t w - Re.limNum II w| ≤ ((D : ℝ) + 1) * (|C'| * |agreeRate t|) :=
    fun w => (hL w).2 t (Real.exp_pos _) hT
  have hb := (formPoly_sub_bound σ (D + 1) (Re.num II t) (Re.limNum II) _ hM).2 c
  have hr : |agreeRate t| ≤ 4 * s := by
    rw [abs_of_nonneg (agreeRate_nonneg s hs)]
    exact hrate s hs hs1
  have hsum : (∑ a, |c a|) ^ (D + 1) ≤ |abelian₂| ^ (D + 1) :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hcL.trans (le_abs_self _)) _
  have hD : (0 : ℝ) ≤ (D : ℝ) + 1 := by positivity
  calc |eval c (Re.FT II t) - eval c (Re.PB II)|
      ≤ (∑ a, |c a|) ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * |agreeRate t|)) := hb
    _ ≤ |abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * (4 * s))) := by
      gcongr
    _ = |abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * 4)) * s := by ring

end GlobalTheory.CompanionTheory.Ar.PB
