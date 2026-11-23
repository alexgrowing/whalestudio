import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.an_two

theorem locUnif {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (s : X → X → ℂ)
    (hO : IsOpen (bdry s)ᶜ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (h : IsRegFamilyC2 A s ph phT) :
    TendstoLocallyUniformlyOn phT ph (𝓝[>] 0) (bdry s)ᶜ := by
  intro u hu x hx
  obtain ⟨j, hj⟩ := A.cover x
  set c := A.chart j with hc
  have hO' : IsOpen (c.target ∩ c.symm ⁻¹' (bdry s)ᶜ) := c.isOpen_inter_preimage_symm hO
  have hz : c x ∈ c.target ∩ c.symm ⁻¹' (bdry s)ᶜ := by
    refine ⟨c.map_source hj, ?_⟩
    show c.symm (c x) ∈ (bdry s)ᶜ
    rw [c.left_inv hj]
    exact hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO' (c x) hz
  have hsub : Metric.closedBall (c x) (r / 2) ⊆ c.target ∩ c.symm ⁻¹' (bdry s)ᶜ :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hunif := (h j (Metric.closedBall (c x) (r / 2)) hsub (isCompact_closedBall _ _)).1
  refine ⟨c.source ∩ c ⁻¹' Metric.ball (c x) (r / 2), ?_, ?_⟩
  · apply nhdsWithin_le_nhds
    exact Filter.inter_mem (c.open_source.mem_nhds hj)
      ((c.continuousAt hj).preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hr)))
  · filter_upwards [hunif u hu] with t ht y hy
    have e : c.symm (c y) = y := c.left_inv hy.1
    have := ht (c y) (Metric.ball_subset_closedBall hy.2)
    simp only [Function.comp] at this
    rw [← hc, e] at this
    exact this

theorem mInt_zero {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) :
    mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt
  split_ifs
  · simp [integralWith]
  · rfl

end PositivityTheory.Xgp.an_two

theorem PositivityTheory.Xgp.t_an_two : ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e (σ ⊕ σ)) (d : σ → S.X → ℝ), (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → ∀ (a : σ) (w : Fin e → σ ⊕ σ), Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x)) (𝓝[>] 0) (𝓝 0) := by
  intro hC e σ S d hd hdiff a w
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have ht0 : 0 < S.t₀ := (S.reg (Sum.inl a)).1
  let f : ℝ → S.X → ℝ := fun t x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x
  let gT : ℝ → S.X → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then f t else 0
  obtain ⟨M, hM⟩ := (isCompact_univ (X := S.X)).exists_bound_of_continuousOn
    (projLine_continuous_of_smooth S.A (hd a)).continuousOn
  set L : S.X → ℝ := fun y => Real.log (rW S.L S.s y) with hL
  have hL1 : ∀ y, 1 ≤ L y := by
    intro y
    have h1 : Real.exp 1 ≤ rW S.L S.s y := by
      have := S.norm_le y
      simp only [rW]
      linarith
    exact (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le h1)).mpr h1
  have hphT : ∀ b, ∀ t, 0 < t → t ≤ S.t₀ → ∀ y ∉ bdry S.s,
      |S.phT b t y| ≤ |S.C| + |S.C₅| * L y := by
    intro b t ht ht' y hy
    obtain ⟨-, -, hr⟩ := S.reg b
    obtain ⟨-, hup, hlow, -⟩ := hr t ht ht'
    obtain ⟨-, -, -, hsw⟩ := S.sing b
    have h1 := (hsw y hy).1
    have h2 := hlow y hy
    have h3 := hup y
    have hL0 : 0 ≤ L y := zero_le_one.trans (hL1 y)
    have h4 : -(|S.C₅| * L y) ≤ -S.C₅ * L y := by
      rw [neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self _) hL0)
    rw [abs_le]
    constructor
    · have := abs_nonneg S.C
      show -(|S.C| + |S.C₅| * L y) ≤ S.phT b t y
      linarith
    · have := le_abs_self S.C
      have := mul_nonneg (abs_nonneg S.C₅) hL0
      linarith
  set C₆ := 2 * |S.C| + 2 * |S.C₅| + |M| with hC₆
  have hcont : ∀ t, ContinuousOn (gT t) (bdry S.s)ᶜ := by
    intro t
    by_cases hp : 0 < t ∧ t ≤ S.t₀
    · have e1 : gT t = f t := if_pos hp
      rw [e1]
      have c1 := projLine_continuous_of_smooth S.A ((S.reg (Sum.inl a)).2.2 t hp.1 hp.2).1
      have c2 := projLine_continuous_of_smooth S.A ((S.reg (Sum.inr a)).2.2 t hp.1 hp.2).1
      have c3 := projLine_continuous_of_smooth S.A (hd a)
      exact ((c1.sub c2).sub c3).continuousOn
    · have e1 : gT t = 0 := if_neg hp
      rw [e1]
      exact continuousOn_const
  have hbound : ∀ t, ∀ y ∉ bdry S.s, |gT t y| ≤ C₆ * Real.log (rW S.L S.s y) := by
    intro t y hy
    have hLy := hL1 y
    have hC6 : 0 ≤ C₆ := by positivity
    show |gT t y| ≤ C₆ * L y
    by_cases hp : 0 < t ∧ t ≤ S.t₀
    · have e1 : gT t = f t := if_pos hp
      rw [e1]
      obtain ⟨l1, u1⟩ := abs_le.mp (hphT (Sum.inl a) t hp.1 hp.2 y hy)
      obtain ⟨l2, u2⟩ := abs_le.mp (hphT (Sum.inr a) t hp.1 hp.2 y hy)
      have a3 : |d a y| ≤ |M| := by
        have := hM y trivial
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self M)
      obtain ⟨l3, u3⟩ := abs_le.mp a3
      have m1 : |S.C| ≤ |S.C| * L y := le_mul_of_one_le_right (abs_nonneg _) hLy
      have m2 : |M| ≤ |M| * L y := le_mul_of_one_le_right (abs_nonneg _) hLy
      have hexp : C₆ * L y = 2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y := by
        rw [hC₆]
        ring
      rw [hexp, abs_le]
      constructor
      · show -(2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y) ≤
          S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y
        linarith
      · show S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y ≤
          2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y
        linarith
    · have e1 : gT t = 0 := if_neg hp
      rw [e1, Pi.zero_apply, abs_zero]
      exact mul_nonneg hC6 (zero_le_one.trans hLy)
  have hO : IsOpen (bdry S.s)ᶜ := (ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry S.sec).isOpen_compl
  have hlim : TendstoLocallyUniformlyOn gT 0 (𝓝[>] 0) (bdry S.s)ᶜ := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨t1, ht1, ev1⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp
      (PositivityTheory.Xgp.an_two.locUnif S.A S.s hO _ _ (S.c2 (Sum.inl a))) (ε / 2) (half_pos hε) x hx
    obtain ⟨t2, ht2, ev2⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp
      (PositivityTheory.Xgp.an_two.locUnif S.A S.s hO _ _ (S.c2 (Sum.inr a))) (ε / 2) (half_pos hε) x hx
    refine ⟨t1 ∩ t2 ∩ (bdry S.s)ᶜ, Filter.inter_mem (Filter.inter_mem ht1 ht2) self_mem_nhdsWithin, ?_⟩
    filter_upwards [ev1, ev2, Ioo_mem_nhdsGT ht0] with t e1 e2 htt y hy
    have e3 : gT t = f t := if_pos ⟨htt.1, htt.2.le⟩
    have hdy := hdiff a y hy.2
    have d1 := e1 y hy.1.1
    have d2 := e2 y hy.1.2
    rw [Real.dist_eq] at d1 d2
    rw [e3, Pi.zero_apply, Real.dist_eq]
    obtain ⟨p1, q1⟩ := abs_lt.mp d1
    obtain ⟨p2, q2⟩ := abs_lt.mp d2
    rw [abs_lt]
    constructor
    · show -ε < 0 - (S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y)
      linarith
    · show 0 - (S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y) < ε
      linarith
  have key := (hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i)) 0 gT C₆ hcont hbound hlim).2
  have hz : mInt S.A (fun i => S.th (w i) + LocPot.ofFun (S.ph (w i))) 0 = 0 :=
    PositivityTheory.Xgp.an_two.mInt_zero _ _
  rw [hz] at key
  refine key.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT ht0] with t ht
  have e1 : gT t = f t := if_pos ⟨ht.1, ht.2.le⟩
  rw [e1]
  rfl
