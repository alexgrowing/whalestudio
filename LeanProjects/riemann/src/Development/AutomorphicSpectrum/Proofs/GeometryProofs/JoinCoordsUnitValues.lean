import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishingStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.OrArch.Ext

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem continuousAt_metric (A : HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContinuousAt A.h z :=
  hA.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hz)

theorem continuous_aeval_form (g : MRing ι) : Continuous fun z : (Σ k, ι k) → ℂ => aeval z g := by
  have := MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) g)
  simpa only [Small.LineModel.eval_map_eq] using this

theorem continuousAt_log_metric {σ : Type} (A : HermLine ι) (hA : IsSmoothHerm A) (c : (Σ k, ι k) → σ)
    {z : σ → ℂ} (hz : ∀ k, ∃ i, z (c ⟨k, i⟩) ≠ 0) :
    ContinuousAt (fun w : σ → ℂ => Real.log (A.h fun p => w (c p))) z := by
  have h1 : ContinuousAt (fun w : σ → ℂ => A.h fun p => w (c p)) z :=
    ContinuousAt.comp (g := A.h) (f := fun (w : σ → ℂ) p => w (c p)) (continuousAt_metric A hA hz)
      (continuous_pi fun p => continuous_apply _).continuousAt
  exact h1.log (A.pos _ hz).ne'

end General

theorem line_smooth {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (t : ℝ)
    (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem archBetween_of_off_form : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : Top.RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Top.Wt Ψ N) (s lo hi : ℝ) (f : MRing (Cmp.joinIdx M.ι R.ι)), f ∉ mCoordIdeal (Ht.joinOf M R i) → (∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j)) → (∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∀ val : Option (Ψ × Fin N) → ℂ, (∀ j, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j) w (val j)) → ∑ j, M.coef lam s j * (Real.log ((M.line t j).h (fun p => w (Cmp.joinInl M.ι R.ι p))) - Real.log ((R.line 1 j).h (fun p => w (Cmp.joinInr M.ι R.ι p))) - Real.log ‖val j‖) ∈ Set.Icc lo hi) → Ht.ArchBetween M R i u t lam s lo hi := by
  intro Ψ _ _ N M R i u t lam s lo hi f hf hu hb z hz val hval
  have hcl := GlobalTheory.T.complex_points_dense_nonvanishing (M.K ⊕ R.K) (Cmp.joinIdx M.ι R.ι) (mCoordIdeal (Ht.joinOf M R i)) _ f
    (GlobalTheory.T.join_model_points_project Ψ N M R i).1 hf
  have hzc := hcl (by rwa [← Small.LineModel.ptsOver_complex])
  have hne : ∀ j, val j ≠ 0 := by
    intro j
    obtain ⟨v, hv0, hv⟩ := hu j ℂ z hz
    rwa [Small.LineModel.hasVal_unique _ _ _ hz (hval j) hv]
  choose dg dh g h hg hh hd e n v using hval
  have hq : ∀ j, aeval z (g j) / aeval z (h j) = val j := fun j => by
    rw [v j, mul_div_assoc, div_self (n j), mul_one]
  let Fn : ((Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ) → ℝ := fun w =>
    ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => w (Cmp.joinInl M.ι R.ι p)) -
      Real.log ((R.line 1 j).h fun p => w (Cmp.joinInr M.ι R.ι p)) -
        Real.log ‖aeval w (g j) / aeval w (h j)‖)
  have hcont : ContinuousAt Fn z := by
    refine tendsto_finset_sum _ fun j _ => ?_
    have h1 := continuousAt_log_metric (M.line t j) (line_smooth M t j) (Cmp.joinInl M.ι R.ι)
      (z := z) fun k => hz.1 (Sum.inl k)
    have h2 := continuousAt_log_metric (R.line 1 j) (line_smooth R 1 j) (Cmp.joinInr M.ι R.ι)
      (z := z) fun k => hz.1 (Sum.inr k)
    have h3 : ContinuousAt (fun w : (Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ =>
        Real.log ‖aeval w (g j) / aeval w (h j)‖) z := by
      refine ContinuousAt.log ?_ ?_
      · exact (((continuous_aeval_form (g j)).continuousAt).div
          ((continuous_aeval_form (h j)).continuousAt) (n j)).norm
      · rw [hq j]
        exact norm_ne_zero_iff.mpr (hne j)
    exact continuousAt_const.mul ((h1.sub h2).sub h3)
  have hev : ∀ᶠ w in 𝓝[{w | w ∈ mcPts (mCoordIdeal (Ht.joinOf M R i)) ∧ Cmp.evC w f ≠ 0}] z,
      Fn w ∈ Set.Icc lo hi := by
    have hV : ∀ᶠ w in 𝓝 z, ∀ j, aeval w (h j) ≠ 0 := by
      rw [Filter.eventually_all]
      intro j
      exact (continuous_aeval_form (h j)).continuousAt.eventually_ne (n j)
    filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with w hw hS
    have hwp : w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)) := by
      rw [Small.LineModel.ptsOver_complex]
      exact hS.1
    exact hb w hwp hS.2 (fun j => aeval w (g j) / aeval w (h j)) fun j =>
      ⟨dg j, dh j, g j, h j, hg j, hh j, hd j, e j, hw j, (div_mul_cancel₀ _ (hw j)).symm⟩
  haveI hnb : (𝓝[{w | w ∈ mcPts (mCoordIdeal (Ht.joinOf M R i)) ∧ Cmp.evC w f ≠ 0}] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hzc
  have hmem : Fn z ∈ Set.Icc lo hi :=
    isClosed_Icc.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hFn : Fn z = ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => z (Cmp.joinInl M.ι R.ι p)) -
      Real.log ((R.line 1 j).h fun p => z (Cmp.joinInr M.ι R.ι p)) - Real.log ‖val j‖) :=
    Finset.sum_congr rfl fun j _ => by rw [hq j]
  rwa [hFn] at hmem

end GlobalTheory.CompanionTheory.Ar.OrArch.Ext
