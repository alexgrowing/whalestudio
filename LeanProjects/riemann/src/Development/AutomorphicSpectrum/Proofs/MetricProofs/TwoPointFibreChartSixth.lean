import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFifthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoByTwoMinorGramIdentityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZeroStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_fin_tail {d : ℕ} (z : Fin (d + 1) → ℂ) :
    AnalyticAt ℂ (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) z := by
  have : (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) =
      ⇑(ContinuousLinearMap.pi fun i : Fin d =>
        (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) := by
    funext u i
    rfl
  rw [this]
  exact ContinuousLinearMap.analyticAt _ z

theorem analyticAt_minorIJ {e N : ℕ} (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (z : Fin e → ℂ)
    (hA : ∀ r s, AnalyticAt ℂ (fun u => A u r s) z) (I J : Finset (Fin N)) :
    AnalyticAt ℂ (fun u => minorIJ (A u) I J) z := by
  unfold minorIJ
  by_cases h : I.card = J.card
  · simp only [h, dite_true, Matrix.det_apply, Matrix.submatrix_apply]
    refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hA _ _)
  · simp only [h, dite_false]
    exact analyticAt_const

theorem analyticAt_facOf {e N : ℕ} (j : ℕ) (a i : Fin N) (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (z : Fin e → ℂ)
    (hA : ∀ r s, AnalyticAt ℂ (fun u => A u r s) z) :
    AnalyticAt ℂ (fun u => facOf N j a (A u) i) z := by
  unfold facOf
  by_cases h₁ : (i : ℕ) + 1 = j
  · by_cases h₂ : (a : ℕ) < j
    · simp only [h₁, h₂, if_true]
      exact analyticAt_minorIJ A z hA _ _
    · simp only [h₁, h₂, if_true, if_false]
      exact analyticAt_const
  · simp only [h₁, if_false]
    exact analyticAt_minorIJ A z hA _ _

theorem fibre_xi_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = xiPot (Gn (Fin.tail z')) (z' 0) + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hD z hz
  have hD' := hD
  obtain ⟨hH, hbc, hbk, hpt, hG, -, -⟩ := hD'
  choose Hp hPa hPe using fun p => GlobalTheory.T.two_point_fibre_chart_fifth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn
    ΦWn l H bp hUn hD p z hz
  have htail : ∀ᶠ z' : Fin (d + 1) → ℂ in 𝓝 z, Fin.tail z' ∈ Un :=
    (analyticAt_fin_tail z).continuousAt.preimage_mem_nhds (hUn.mem_nhds hz)
  have hHa : ∀ τ' r s, AnalyticAt ℂ (fun u => H τ' (Fin.tail u) r s) z := fun τ' r s =>
    AnalyticAt.comp (g := fun w => H τ' w r s) (hH τ' r s _ hz) (analyticAt_fin_tail z)
  have hfac : ∀ i : Fin N, ∃ A : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ A z ∧ ∀ᶠ z' in 𝓝 z,
      (if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) = (A z').re := by
    intro i
    by_cases hp : IsProperStep N j i
    · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => by simp [hp]⟩
    · obtain ⟨A, hA, hAe⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => facOf N j a (H τ (Fin.tail u)) i) z
        (analyticAt_facOf j a i (fun u => H τ (Fin.tail u)) z (hHa τ))
        (GlobalTheory.T.step_factor_ne_zero N j a i _ ((hpt _ hz).2 τ).1 ((hpt _ hz).2 τ).2)
      exact ⟨A, hA, hAe.mono fun z' h => by simpa [hp] using h⟩
  have hups : ∀ i : Fin N, ∃ A : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ A z ∧ ∀ᶠ z' in 𝓝 z,
      upsLogAt BM l (τ, i) (bp (Fin.tail z')) = (A z').re := by
    intro i
    by_cases hp : M.blk (τ, i) = none
    · have hO : bp (Fin.tail z) ∈ BM.O l := (hpt _ hz).1.1
      have hreg := ((BM.good l _ hO).2.2 (τ, i) hp).2.1
      have hv := GlobalTheory.T.regular_function_analytic_on_chart (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x ((BM.F l).υ (τ, i)) d n BM.Rb Un bp (Fin.tail z)
        hUn hz hbc hbk hreg
      have hf : AnalyticAt ℂ (fun u => upsVal BM l (τ, i) (bp (Fin.tail u))) z :=
        AnalyticAt.comp (g := fun w => valAt M.x ((BM.F l).υ (τ, i)) (BM.Rb.lift (bp w) (bp w))) hv
          (analyticAt_fin_tail z)
      obtain ⟨A, hA, hAe⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) _ z hf
        (GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) _ hO hp)
      exact ⟨A, hA, hAe.mono fun z' h => by simpa [upsLogAt, hp] using h⟩
    · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => by simp [upsLogAt, hp]⟩
  choose Lf hLa hLe using hfac
  choose Uf hUa hUe using hups
  refine ⟨fun u => ∑ p, ((xiCoef τ a p : ℝ) : ℂ) * Hp p u -
    ∑ i, ((xiCoef τ a (τ, i) : ℝ) : ℂ) * (Lf i u + Uf i u), ?_, ?_⟩
  · refine AnalyticAt.sub (Finset.analyticAt_fun_sum _ fun p _ => analyticAt_const.mul (hPa p))
      (Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ((hLa i).add (hUa i)))
  · filter_upwards [htail, eventually_all.2 hPe, eventually_all.2 hLe, eventually_all.2 hUe] with z' hw h1 h2 h3
    have hs : ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) =
        xiPot (Gn (Fin.tail z')) (z' 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
          ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) +
            upsLogAt BM l (τ, i) (bp (Fin.tail z'))) :=
      GlobalTheory.T.two_by_two_minor_gram_identity Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp (Fin.tail z'))) (fun τ' => H τ' (Fin.tail z'))
        (fun p => upsLogAt BM l p (bp (Fin.tail z'))) (z' 0) (Gn (Fin.tail z')) M.j_le hb hab hca hcb
        (BM.G_pos l τ _ (hpt _ hw).1).1 (BM.G_pos l τ _ (hpt _ hw).1).2 ((hpt _ hw).2 τ).1 ((hpt _ hw).2 τ).2
        (hG _ hw)
    have e1 : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') =
        ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) +
          ∑ p, (xiCoef τ a p : ℝ) * (Hp p z').re := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by rw [h1 p, mul_add]
    have e3 : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
          ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) +
            upsLogAt BM l (τ, i) (bp (Fin.tail z'))) =
        ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((Lf i z').re + (Uf i z').re) :=
      Finset.sum_congr rfl fun i _ => by rw [h2 i, h3 i]
    rw [e1, hs, e3]
    simp only [Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
