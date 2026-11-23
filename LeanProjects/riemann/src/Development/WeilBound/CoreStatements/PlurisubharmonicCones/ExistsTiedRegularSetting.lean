import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMaxOscillation
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMollifierLowerBound
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartComparison
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPolyMaxLowerBound
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PCutoffs
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothConjInvariantMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPotentialChartsWithRadiiStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeMetricFramePropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgePotentialSmoothOffBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPotentialFromSncChartsStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExpLeLogR

namespace LevelTowerAlt.Reg

open Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights.Regular
open ReciprocityTheory.AnForm.A (IsPsh coordDiv)
open scoped ContDiff

section Ratio

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {d : ℕ}

noncomputable def logRat (M : CxModel P d) (A R : HermLine J) (x : M.Xc) : ℝ :=
  Real.log (A.h (M.surj x).choose) - Real.log (R.h (M.surj x).choose)

theorem logRat_proj (M : CxModel P d) {A R : HermLine J} (h : R.a = A.a) {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts P) : logRat M A R (M.proj z) = Real.log (A.h z) - Real.log (R.h z) := by
  obtain ⟨hw, he⟩ := (M.surj (M.proj z)).choose_spec
  obtain ⟨c, hc, hcz⟩ := (M.fibre z hz _ hw).1 he.symm
  have hp := (prod_norm_zpow_pos hc A.a).ne'
  unfold logRat
  rw [hcz]
  change Real.log (A.h fun p => c p.1 * z p) - Real.log (R.h fun p => c p.1 * z p) = _
  rw [A.smul c z hc, R.smul c z hc, h, Real.log_mul hp (A.pos z hz.1).ne', Real.log_mul hp (R.pos z hz.1).ne']
  ring

theorem exists_bound_log {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {R : HermLine J}
    (hR : IsSmoothHerm R) : ∃ Q : ℝ, ∀ s : Fin n → ℂ, ‖s‖ ≤ 3 / 4 → |Real.log (R.h (χ.γ s))| ≤ Q := by
  have hsub : closedBall (0 : Fin n → ℂ) (3 / 4) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have h1 : ContinuousOn (fun s => R.h (χ.γ s)) (closedBall (0 : Fin n → ℂ) (3 / 4)) :=
    hR.continuousOn.comp (χ.analytic.continuousOn.mono hsub) fun s hs => (χ.mem s (hsub hs)).1
  obtain ⟨Q, hQ⟩ := (isCompact_closedBall (0 : Fin n → ℂ) (3 / 4)).exists_bound_of_continuousOn
    (h1.log fun s hs => (R.pos _ (χ.mem s (hsub hs)).1).ne')
  exact ⟨Q, fun s hs => hQ s (mem_closedBall_zero_iff.2 hs)⟩

end Ratio

theorem exists_radius {n : ℕ} (t₀ : Fin n → ℂ) {e : ℝ} (he : 0 < e) :
    ∃ r > (0 : ℝ), r ≤ e ∧ ∀ i, t₀ i ≠ 0 → r ≤ ‖t₀ i‖ := by
  have h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i, t₀ i ≠ 0 → r ≤ ‖t₀ i‖ := eventually_all.2 fun i => by
    by_cases hi : t₀ i = 0
    · exact Eventually.of_forall fun _ h => absurd hi h
    · filter_upwards [Ioc_mem_nhdsGT (norm_pos_iff.2 hi)] with r hr _ using hr.2
  obtain ⟨r, hr⟩ := (h.and (Ioc_mem_nhdsGT he)).exists
  exact ⟨r, hr.2.1, hr.2.2, hr.1⟩

noncomputable def starL (n : ℕ) : (Fin n → ℂ) →L[ℝ] Fin n → ℂ :=
  ContinuousLinearMap.pi fun i => Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj i)

theorem margin_tendsto (C : ℝ) :
    Tendsto (fun t : ℝ => max t (C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => Real.log (Real.log t⁻¹) / Real.log t⁻¹) (𝓝[>] 0) (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have h2 := h0.max ((h1.const_mul C).add (h0.const_mul C))
  simpa [mul_div_assoc] using h2

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

theorem exists_tied {M : XModel D} {A ref : HermLine J} (hra : ref.a = A.a) (hrs : IsSmoothHerm ref)
    (R : RegChartData M.atlas) (hth : ThRef M ref R.th)
    (hY : ∀ x ∈ R.Yo, ∃ z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y), M.proj z = x)
    (hph : ∀ z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y), M.proj z ∈ R.Yo →
      R.ph (M.proj z) = Real.log (A.h z) - Real.log (ref.h z)) :
    ∃ S : LogLogRegularisationSetting M D.Xo A, S.IsTied := by
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D.n
  obtain ⟨cut, Cc, hcut⟩ := CutoffsExist.proof M.Xc D.n M.atlas R.toPotentialCharts
  obtain ⟨C, t₀, ht₀, hcmp⟩ := ChartComparison.proof MollifiedLowerBound.closed PolyMaxOscillation.proof_closed
    PolyMaxLowerBound.proof TruncPsh.proof TruncTransfer.proof M.Xc D.n M.atlas R ρ
  have hll : Tendsto (fun t : ℝ => Real.log (Real.log t⁻¹)) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  refine ⟨{ ref := ref, ref_deg := hra, ref_smooth := hrs, R := R, th_ref := hth, Yo_sub := hY, ph_eq := hph,
            ρ := ρ, η := cut, Cη := Cc, cutoff := hcut,
            K := fun t => (|C| + |R.Clog| + 1) * Real.log (Real.log t⁻¹),
            e1 := fun t => max t (C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t),
            e1_ge := fun _ _ => le_max_left _ _ }, margin_tendsto C,
    hll.const_mul_atTop (by positivity), ?_, ?_⟩
  · filter_upwards [hll.eventually_ge_atTop 0] with t ht
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self R.Clog, abs_nonneg C]) ht
  · filter_upwards [hll.eventually_ge_atTop 0, Ioo_mem_nhdsGT ht₀] with t h0 ht j k x hx
    exact (hcmp t ht.1 ht.2 _ (mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self C, abs_nonneg R.Clog]) h0) j k x hx).trans (le_max_right _ _)

theorem mem_Yo {M : XModel D} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (∃ z' ∈ D.Xo, M.proj z' = M.proj z) ↔ z ∉ D.Bd := by
  refine ⟨?_, fun h => ⟨z, ⟨hz, h⟩, rfl⟩⟩
  rintro ⟨z', hz', e⟩ hB
  obtain ⟨c, hc, rfl⟩ := (M.fibre z hz z' hz'.1).1 e.symm
  exact hz'.2 (D.bd_torus z hB c hc)

theorem main (Hd : HodgeData D) (M : XModel D) (hP : ChartPsh D (phMu Hd)) :
    ∃ S : LogLogRegularisationSetting M D.Xo (muLine Hd), S.IsTied := by
  classical
  obtain ⟨ref, hra, hrs, hrc⟩ := GlobalTheory.T.exists_smooth_conj_invariant_metric K J Hd.aMu
  obtain ⟨hsm, hbd⟩ := GlobalTheory.T.hodge_potential_smooth_off_boundary K J II Ψ Ω W D Hd
  obtain ⟨-, -, -, hO⟩ := GlobalTheory.T.hodge_metric_frame_properties K J II Ψ Ω W D Hd
  have hrad : ∀ (a : Fin D.nCharts) (t₀ : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), ∃ r > (0 : ℝ), (∀ i, t₀ i ≠ 0 → r ≤ ‖t₀ i‖) ∧
      (‖t₀‖ ≤ 1 / 2 → ∃ C > (0 : ℝ), ∀ t ∈ offBd D a, ‖t - t₀‖ < r →
        -(C * Real.log ((D.chart a).logR t)) ≤ phMu Hd ((D.chart a).γ t) ∧ phMu Hd ((D.chart a).γ t) ≤ C ∧
          ‖fderiv ℝ (fun s => phMu Hd ((D.chart a).γ s)) t‖ ≤
            C * (D.chart a).logR t ^ C * Real.exp ((D.chart a).logR t / 2)) := by
    intro a t₀
    by_cases h : ‖t₀‖ ≤ 1 / 2
    · obtain ⟨e, he, C, hC, hb⟩ := hbd a t₀ h
      obtain ⟨r, hr, hre, hri⟩ := exists_radius t₀ he
      exact ⟨r, hr, hri, fun _ => ⟨C, hC, fun t ht h' => hb t ht (h'.trans_le hre)⟩⟩
    · obtain ⟨r, hr, -, hri⟩ := exists_radius t₀ one_pos
      exact ⟨r, hr, hri, fun h' => absurd h' h⟩
  choose r hr hri hrb using hrad
  obtain ⟨P, S, -, hth, had, hsnc, -, hpc⟩ := GlobalTheory.T.exists_potential_charts_with_radii K J II Ψ Ω W D M ref r hrs hrc hr
  obtain ⟨rf, f, Bf, hr1, hf, hrf⟩ := GlobalTheory.T.exists_potential_from_snc_charts K J II Ψ Ω W D M P S had hsnc
  let ph : M.Xc → ℝ := logRat M (muLine Hd) ref
  have hph : ∀ z ∈ mcPts (mCoordIdeal D.y), ph (M.proj z) = phMu Hd z - Real.log (ref.h z) :=
    fun z hz => logRat_proj M hra hz
  have hT : ∀ j, (P.chart j).target = ball 0 1 := fun j => (hsnc j).1
  have key : ∀ j, ContDiffOn ℝ ∞ (fun y => P.q j y + ph ((P.chart j).symm y)) (ball 0 1 \ coordDiv (S j)) ∧
      IsPsh (ball 0 1 \ coordDiv (S j)) (fun y => P.q j y + ph ((P.chart j).symm y)) ∧
      ∃ C' c : ℝ, 0 < C' ∧ ∀ t ∈ ball (0 : Fin D.n → ℂ) 1 \ coordDiv (S j), ∀ ρ : ℝ,
        Real.exp 1 + c + ∑ i ∈ S j, Real.log (‖t i‖ ^ 2)⁻¹ ≤ ρ →
          ph ((P.chart j).symm t) ≤ C' ∧ -C' * Real.log ρ ≤ ph ((P.chart j).symm t) ∧
            ‖fderiv ℝ (fun y => P.q j y + ph ((P.chart j).symm y)) t‖ ≤ C' * ρ ^ C' * Real.exp (ρ / 2) := by
    intro j
    obtain ⟨a, t₀, ε, h₀, hε, hεr, hε', hγ⟩ := hpc j
    have hsep : ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖ := fun i hi => hεr.trans (hri a t₀ i hi)
    have hS := had.mem_iff_of_piece (hT j) h₀ hε hε' (fun i _ => hsep i)
      (hγ.imp (fun h t ht => (h t ht).1) fun h t ht => (h t ht).1)
    obtain ⟨C, hC, hb⟩ := hrb a t₀ h₀
    obtain ⟨Q, hQ⟩ := exists_bound_log (n := D.n) (D.chart a) hrs
    have hn : ∀ t : Fin D.n → ℂ, ‖t‖ < 1 → ‖t₀ + (ε : ℂ) • t‖ ≤ 3 / 4 := fun t ht => by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε.le]
      nlinarith [norm_nonneg t]
    have hm : ∀ t : Fin D.n → ℂ, ‖t‖ < 1 → (D.chart a).γ (t₀ + (ε : ℂ) • t) ∈ mcPts (mCoordIdeal D.y) :=
      fun t ht => (D.chart a).mem _ (SncPiece.add_smul_mem_ball h₀ hε hε' (ht.trans one_lt_two))
    rw [hT j] at hγ
    rcases hγ with hγ | hγ
    · refine piece (n := D.n) (D.chart a) (SncPiece.isOpen_offBd D a) (hsm a) (hP a) h₀ hε hε' hsep hC
        (fun t ht h' => hb t ht (h'.trans_le hεr)) (ContinuousLinearMap.id ℝ _) (fun _ _ => rfl)
        (fun _ _ h => h) hS (Q := Q) (fun t ht => ?_) (fun t ht _ => ?_)
      · rw [(hγ t ht).2]
        exact hQ _ (hn t (mem_ball_zero_iff.1 ht))
      · rw [(hγ t ht).1, (hγ t ht).2, hph _ (hm t (mem_ball_zero_iff.1 ht))]
        exact add_sub_cancel _ _
    · refine piece (n := D.n) (D.chart a) (SncPiece.isOpen_offBd D a) (hsm a) (hP a) h₀ hε hε' hsep hC
        (fun t ht h' => hb t ht (h'.trans_le hεr)) (starL _) (fun _ _ => norm_star _)
        (fun _ _ h => isPsh_star h) hS (Q := Q) (fun t ht => ?_) (fun t ht hB => ?_)
      · rw [(hγ t ht).2]
        exact hQ _ (hn _ (by rw [norm_star]; exact mem_ball_zero_iff.1 ht))
      · have hz := hm (star t) (by rw [norm_star]; exact mem_ball_zero_iff.1 ht)
        have e1 : ref.h (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t))) = _ := hrc _
        rw [(hγ t ht).1, (hγ t ht).2, hph _ (SncPiece.conj_mem hz), hO _ ⟨hz, hB⟩, e1]
        exact add_sub_cancel _ _
  choose hks hkp C' c hC' hk using key
  set Cs : ℝ := ∑ j, C' j with hCs
  set cs : ℝ := |Bf| + ∑ j, |c j| with hcs
  have hCle : ∀ j, C' j ≤ Cs := fun j => Finset.single_le_sum (fun i _ => (hC' i).le) (Finset.mem_univ j)
  have hcle : ∀ j, |c j| ≤ ∑ j, |c j| := fun j =>
    Finset.single_le_sum (f := fun j => |c j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hcs0 : 0 ≤ cs := by positivity
  let Yo : Set M.Xc := {x | ∃ z ∈ D.Xo, M.proj z = x}
  have hYo : ∀ j, ∀ x ∈ (P.chart j).source, x ∈ Yo ↔ P.chart j x ∉ coordDiv (S j) := by
    intro j x hx
    obtain ⟨z, hz, rfl⟩ := M.surj x
    exact (mem_Yo hz).trans (had j z hz hx).not
  have hr1' : ∀ x ∈ Yo, 1 ≤ rf x + cs := by
    rintro _ ⟨z, hz, rfl⟩
    linarith [hr1 z hz]
  have hk' : ∀ j, ∀ t ∈ (P.chart j).target \ coordDiv (S j),
      ph ((P.chart j).symm t) ≤ Cs ∧ -Cs * Real.log (rf ((P.chart j).symm t) + cs) ≤ ph ((P.chart j).symm t) ∧
        ‖fderiv ℝ (fun y => P.q j y + ph ((P.chart j).symm y)) t‖ ≤
          Cs * (rf ((P.chart j).symm t) + cs) ^ Cs * Real.exp ((rf ((P.chart j).symm t) + cs) / 2) := by
    intro j t ht
    have h1 := hr1' _ ((hYo j _ ((P.chart j).map_target ht.1)).2 (by rw [(P.chart j).right_inv ht.1]; exact ht.2))
    obtain ⟨b1, b2, b3⟩ := hk j t (hT j ▸ ht) (rf ((P.chart j).symm t) + cs) (by
      rw [hrf j t ht]
      linarith [(abs_le.1 ((hf j).2 t ht.1)).1, le_abs_self Bf, le_abs_self (c j), hcle j])
    refine ⟨b1.trans (hCle j), le_trans ?_ b2, b3.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (neg_le_neg (hCle j)) (Real.log_nonneg h1)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul (hCle j) (Real.rpow_le_rpow_of_exponent_le h1 (hCle j))
        (Real.rpow_nonneg (by linarith) _) ((hC' j).le.trans (hCle j))) (Real.exp_pos _).le
  have hpt : ∀ x ∈ Yo, ∃ j, x ∈ (P.chart j).source ∧ P.chart j x ∈ (P.chart j).target \ coordDiv (S j) := by
    intro x hx
    obtain ⟨j, hj⟩ := P.cover x
    have hs := P.mid_subset_source j (P.inner_subset_mid j hj)
    exact ⟨j, hs, (P.chart j).map_source hs, (hYo j x hs).1 hx⟩
  have hsmooth : M.atlas.SmoothOn Yo ph := by
    intro k y hy
    obtain ⟨j, hs, ht⟩ := hpt _ hy.2
    have hV : IsOpen ((P.chart j).target \ coordDiv (S j)) :=
      (P.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
    have h1 : ContDiffOn ℝ ∞ (fun y => ph ((P.chart j).symm y)) ((P.chart j).target \ coordDiv (S j)) := by
      have h2 := hks j
      rw [← hT j] at h2
      exact (h2.sub ((P.q_smooth j).mono Set.diff_subset)).congr fun y _ => by simp
    have h3 : ContDiffAt ℝ ∞ (P.chart j ∘ (M.atlas.chart k).symm) y :=
      (((P.compat j k).1 y ⟨hy.1, hs⟩).restrictScalars (𝕜 := ℝ)).contDiffAt
    have h4 : ∀ᶠ y' in 𝓝 y, (M.atlas.chart k).symm y' ∈ (P.chart j).source :=
      ((M.atlas.chart k).continuousAt_symm hy.1).preimage_mem_nhds ((P.chart j).open_source.mem_nhds hs)
    refine (((h1.contDiffAt (hV.mem_nhds ht)).comp y h3).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [h4] with y' hy'
    simp [(P.chart j).left_inv hy']
  let R : RegChartData M.atlas :=
    { toPotentialCharts := P, S := S, Yo := Yo, mem_Yo := hYo, ph := ph, ph_smooth := hsmooth,
      u_psh := fun j => by rw [hT j]; exact hkp j
      r := fun x => rf x + cs
      one_le_r := hr1'
      f := fun j y => f j y + cs
      f_smooth := fun j => (hf j).1.add contDiffOn_const
      f_bdd := ⟨Bf + cs, fun j y hy => (abs_add_le _ _).trans
        (add_le_add ((hf j).2 y hy) (abs_of_nonneg hcs0).le)⟩
      r_chart := fun j y hy => by rw [hrf j y hy]; ring
      Clog := Cs
      Cph := Cs
      ph_le := fun x hx => by
        obtain ⟨j, hs, ht⟩ := hpt x hx
        have := (hk' j _ ht).1
        rwa [(P.chart j).left_inv hs] at this
      ph_ge := fun x hx => by
        obtain ⟨j, hs, ht⟩ := hpt x hx
        have := (hk' j _ ht).2.1
        rwa [(P.chart j).left_inv hs] at this
      Cgrad := Cs
      grad_le := fun j y hy => (hk' j y hy).2.2 }
  refine exists_tied (A := muLine Hd) hra hrs R hth ?_ fun z hz _ => hph z hz.2
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz, hz.1⟩, rfl⟩

end LevelTowerAlt.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem LevelTowerAlt.exists_tied_regular_setting : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D), ChartPsh D (phMu Hd) → ∃ S : LogLogRegularisationSetting M D.Xo (muLine Hd), S.IsTied :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hd M hP => LevelTowerAlt.Reg.main Hd M hP
