import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricVectorLogResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointInMultiprojectivePointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFlagPointInOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicCompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PlkFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensR

variable {K : Type} {ι : K → Type}

theorem orbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [hc p.1]

theorem orbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem orbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem analytic_minorIJ {m N : ℕ} {V : Set (Fin m → ℂ)} {h : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ r s, AnalyticOnNhd ℂ (fun u => h u r s) V) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun u => minorIJ (h u) I J) V := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply', Matrix.submatrix_apply]
    refine Finset.analyticOnNhd_fun_sum _ fun σ _ => ?_
    exact analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun i _ => hh _ _)
  · simp only [dif_neg e]
    exact analyticOnNhd_const

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensR

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

open DensR in

theorem dens_r : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x : FA.Re.R.X), FA.pr (FA.Re.π x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (FA.Re.π x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x'))) (FA.Re.R.lift x' x') p ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l x hx V hV hxV
  have hlift : FA.Re.R.lift x x ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x x (FA.Re.R.mem_U x)
  obtain ⟨h₀, hh₀, hso₀⟩ := GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l (FA.pr (FA.Re.π x)) hx _ hlift (FA.pr_eq x)
  have hgood := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l
  have han : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X)
      (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ), IsOpen V → ContinuousOn bp V →
      (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) →
      (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) →
      (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) →
      ∀ q, AnalyticOnNhd ℂ (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) q) V := by
    intro m V bp hh hV hc ha hm hhan _ q
    have hval := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l m V bp hV hc ha hm
    by_cases hk : ∀ p, M.blk p ≠ some q.1
    · simp only [FC.flagPt, dif_pos hk]
      exact hval.1 _
    · simp only [FC.flagPt, dif_neg hk]
      refine Finset.analyticOnNhd_fun_sum _ fun I _ => ?_
      refine (hval.2 _ fun b hb => ((hgood b hb).2.1.2.1 q I).1).mul ?_
      exact analytic_minorIJ (fun r s => hhan _ r s) _ _
  obtain ⟨x', hx'V, b', hb', h', hh', hso', hmin⟩ :=
    GlobalTheory.T.base_metric_vector_log_resolution K ι Φ y Ψ N j M n BM K ι (mCoordIdeal y) FA.Re.J (d + 1) FA.Re.R FA.J_top l
      (fun b h => FC.flagPt M (BM.F l) (FC.bvec BM l b) h) (fun _ => 1)
      (fun _ => ⟨fun a => by simp, fun a b hab => Matrix.one_apply_ne hab.ne⟩) han
      (fun b hb h hh => GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l b hb h hh)
      x _ hx h₀ hh₀ hso₀ V hV hxV
  have hg' := hgood b' hb'.1
  have hpr : FA.pr (FA.Re.π x') = b' := by
    refine BM.Rb.inj _ _ (fun hc => by simpa using hc.2 1 Submodule.mem_top) ?_
    refine orbit_trans (orbit_symm (FA.pr_eq x')) (orbit_trans (orbit_basePart M.blk hso') ?_)
    rw [FC.basePart_flagPt]
    exact hg'.2.2.2
  refine ⟨x', hx'V, hpr ▸ hb', fun p => ?_⟩
  rw [hpr]
  rw [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hso']
  cases hp : M.blk p with
  | none => simp [FC.plk, hp]
  | some k =>
    have hprop : IsProperStep N j p.2 := by
      by_contra hc
      have := (M.blk_none p).2 hc
      simp [hp] at this
    rw [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h' p k (BM.isFrame l) hg'.1 hg'.2.1
      (fun τ' => (hh' τ').1) hp]
    exact (hmin p.1 p.2 hprop).1

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
