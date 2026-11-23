import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticOrbitOffBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointInMultiprojectivePointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecompositionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

theorem analyticAt_detFac {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin N)
    {H : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : ∀ r s, AnalyticAt ℂ (fun u => H u r s) w) :
    AnalyticAt ℂ (fun u => detFac j i (H u)) w := by
  unfold detFac
  refine AnalyticAt.mul ?_ ?_
  · split_ifs
    · exact Fib.analyticAt_minorIJ_of_entries _ w h _ _
    · exact analyticAt_const
  · split_ifs
    · exact Fib.analyticAt_minorIJ_of_entries _ w h _ _
    · exact analyticAt_const

theorem holoOn_mul {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {W : Set X}
    {P Q : X → Matrix (Fin N) (Fin N) ℂ} (hP : ∀ a b, A.HoloOn W fun x => P x a b)
    (hQ : ∀ a b, A.HoloOn W fun x => Q x a b) (a b : Fin N) : A.HoloOn W fun x => (P x * Q x) a b := by
  intro k t ht
  show AnalyticAt ℂ (fun w => (P ((A.chart k).symm w) * Q ((A.chart k).symm w)) a b) t
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => (hP a c k t ht).mul (hQ c b k t ht)

theorem period_chart (FA : FlagAn BM d) (hsurj : Function.Surjective FA.Re.π) {l : Fin BM.q} {Vb : Set BM.Rb.X}
    {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ} (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) {W : Set FA.S.X}
    (hW : IsOpen W) {x : FA.S.X} (hx : x ∈ W) (hl : ∀ x' ∈ W, FA.pr x' ∈ BM.O l \ bdry BM.s ∧ FA.pr x' ∈ Vb)
    {H : Ψ → FA.S.X → Matrix (Fin N) (Fin N) ℂ} (hH : ∀ τ a b, FA.S.A.HoloOn W fun x' => H τ x' a b)
    (hHb : ∀ τ, ∀ x' ∈ W, IsBlockDiag j (H τ x') ∧ (H τ x').det ≠ 0)
    (ho : ∀ x' ∈ W, ∀ x₀, FA.Re.π x₀ = x' →
      SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x')) fun τ => H τ x')) :
    ∃ V, IsPeriodChart (FA.S.comap some).A j (FA.S.comap some).potH x V fun τ x' => Pi τ (FA.pr x') * H τ x' := by
  have hj := M.j_le
  have hg := GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l
  have hl1 : ∀ x' ∈ W, FA.pr x' ∈ BM.O l := fun x' h => (hl x' h).1.1
  have hbv := bvec_holo BM FA.pr_holo hW hl1
  have hst := fun (p : Ψ × Fin N) x' (hx' : x' ∈ W) => GlobalTheory.T.flag_potential_block_decomposition N j p.2 (Pi p.1 (FA.pr x'))
    (BM.G l p.1 (FA.pr x')) (H p.1 x') hj (hPi.2.2 p.1 _ (hl x' hx').2) (BM.G_pos l p.1 _ (hl x' hx').1).1
    (BM.G_pos l p.1 _ (hl x' hx').1).2 (hHb p.1 x' hx').1 (hHb p.1 x' hx').2
  obtain ⟨k, hk⟩ := FA.S.A.cover x
  set c := FA.S.A.chart k with hc
  have hO : IsOpen (c.target ∩ c.symm ⁻¹' W) := c.isOpen_inter_preimage_symm hW
  have hxO : c x ∈ c.target ∩ c.symm ⁻¹' W := ⟨c.map_source hk, by simpa [c.left_inv hk] using hx⟩
  have hsx : c.symm (c x) = x := c.left_inv hk
  have key : ∀ p : Ψ × Fin N, ∃ V : Set FA.S.X, IsOpen V ∧ x ∈ V ∧ ∃ G : FA.S.X → ℂ, FA.S.A.HoloOn V G ∧
      ∀ x' ∈ V, ((FA.S.comap some).potH p).φ x x' - stepPot N j p.2 (Pi p.1 (FA.pr x') * H p.1 x') = (G x').re := by
    intro p
    obtain ⟨H1, hH1, he1⟩ := GlobalTheory.T.local_holomorphic_lift_realisation K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re (some p) (d + 1)
      (c.target ∩ c.symm ⁻¹' W) c.symm
      (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (c.symm u))) fun τ => H τ (c.symm u)) (c x)
      FA.J_top FA.deg_one FA.br_empty hO hxO
      (fun q u hu => analyticAt_flagPt (BM.F l) (fun q => hbv.1 q k u hu)
        (fun q I => hbv.2 _ (fun b hb => ((hg b hb).2.1.2.1 q I).1) k u hu) (fun τ r s => hH τ r s k u hu) q)
      (fun u hu => GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l _ (hl1 _ hu.2) _ fun τ => hHb τ _ hu.2)
      (fun u hu x₀ h => ho _ hu.2 x₀ h)
    obtain ⟨H2, hH2, he2⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => detFac j p.2 (H p.1 (c.symm u))) (c x)
      (analyticAt_detFac p.2 fun r s => hH p.1 r s k _ hxO)
      (CPts.detFac_ne_zero hj p.2 (hHb p.1 _ hxO.2).1 (hHb p.1 _ hxO.2).2)
    obtain ⟨H3, hH3, he3⟩ : ∃ H3 : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ H3 (c x) ∧
        ∀ᶠ u in 𝓝 (c x), Fib.upsLogAt BM l p (FA.pr (c.symm u)) = (H3 u).re := by
      by_cases hp : M.blk p = none
      · simp only [Fib.upsLogAt, if_pos hp]
        refine GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => Fib.upsVal BM l p (FA.pr (c.symm u))) (c x) ?_
          (GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l p _ (hl1 _ hxO.2) hp)
        exact GlobalTheory.T.regular_function_analytic_on_chart _ _ M.Ω M.x ((BM.F l).υ p) (d + 1) n BM.Rb (c.target ∩ c.symm ⁻¹' W) (FA.pr ∘ c.symm) (c x)
          hO hxO (FA.pr_holo.1.comp_continuousOn (c.continuousOn_symm.mono Set.inter_subset_left))
          (fun m => (FA.pr_holo.2 k m).mono fun t ht => ⟨ht.1.1, ht.2⟩)
          ((BM.good l _ (hl1 _ hxO.2)).2.2 p hp).2.1
      · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun u => by simp [Fib.upsLogAt, hp]⟩
    refine exists_holoOn_of_germ FA.S.A hk (H := fun u => H1 u - H2 u - H3 u) ((hH1.sub hH2).sub hH3) ?_
    filter_upwards [he1, he2, he3, hO.mem_nhds hxO] with u h1 h2 h3 hu
    obtain ⟨x₀, hx₀⟩ := hsurj (c.symm u)
    have hline := GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ _ (FA.pr (c.symm u)) p (H p.1 (c.symm u))
      (hl _ hu.2).1 (ho _ hu.2 x₀ hx₀) (by rw [FC.basePart_flagPt]; exact (hg _ (hl1 _ hu.2)).2.2.2)
      (FC.exactAt_flagPt M (BM.F l) (hg _ (hl1 _ hu.2)).2.2.1 (fun τ => H τ (c.symm u)) p)
      (hHb _ _ hu.2).1 (hHb _ _ hu.2).2
    have hphi : ((FA.S.comap some).potH p).φ x (c.symm u) =
      (FA.S.th (some p)).φ x (c.symm u) + FA.S.ph (some p) (c.symm u) := rfl
    rw [hsx, FA.ref_some] at h1
    rw [hx₀, Fib.potAt] at hline
    rw [hphi, h1, (hst p _ hu.2).2, Complex.sub_re, Complex.sub_re, ← h2, ← h3]
    linarith
  choose V hVo hxV G hG hGe using key
  refine ⟨W ∩ ⋂ p, V p, hW.inter (isOpen_iInter_of_finite hVo), ⟨hx, Set.mem_iInter.2 hxV⟩, fun τ a b => ?_,
    fun τ x' hx' => ?_, fun p => ⟨G p, holoOn_mono (hG p) fun x' hx' => Set.mem_iInter.1 hx'.2 p, fun x' hx' => ?_⟩⟩
  · refine holoOn_mono (holoOn_mul (W := W) (fun a b => ?_) (hH τ) a b) Set.inter_subset_left
    exact holoOn_mono (holoOn_comp FA.pr_holo (hPi.2.1 τ a b)) fun x' hx' => (hl x' hx').2
  · exact StepBlock.inFlagDomain_mul (hPi.2.2 τ _ (hl x' hx'.1).2).1 (hHb τ x' hx'.1).1 (hHb τ x' hx'.1).2
  · have := hGe p x' (Set.mem_iInter.1 hx'.2 p)
    linarith

end PositivityTheory.Xgp.c_unif
