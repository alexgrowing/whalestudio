import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem pshPull {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) {O : Set X} (hO : IsOpen O)
    {f : X → ℝ} (hf : A.SmoothOn O f)
    (hl : ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' O, ∀ w : Fin e → ℂ,
      0 ≤ levi (f ∘ (A.chart j).symm) y w)
    (a : Fin e → ℂ) (c : ℂ) {V : Set (Fin e → ℂ)} (hV : IsOpen V)
    (hVT : ∀ z ∈ V, a + c • z ∈ ψ.target ∧ ψ.symm (a + c • z) ∈ O) :
    ContinuousOn (fun z => f (ψ.symm (a + c • z))) V ∧
      ReciprocityTheory.AnForm.A.IsPsh V (fun z => f (ψ.symm (a + c • z))) := by
  have key : ∀ z ∈ V, ContDiffAt ℝ 2 (fun z => f (ψ.symm (a + c • z))) z ∧
      ∀ w, 0 ≤ levi (fun z => f (ψ.symm (a + c • z))) z w := by
    intro z hz
    obtain ⟨h1, h2⟩ := hVT z hz
    have hTa : AnalyticAt ℂ (fun z : Fin e → ℂ => a + c • z) z :=
      by
      have h : AnalyticAt ℂ (fun z : Fin e → ℂ => (c • ContinuousLinearMap.id ℂ (Fin e → ℂ)) z) z :=
        ContinuousLinearMap.analyticAt _ z
      exact analyticAt_const.add (by simpa using h)
    obtain ⟨j, hj⟩ := A.cover (ψ.symm (a + c • z))
    have hτa : AnalyticAt ℂ ((A.chart j ∘ ψ.symm) ∘ fun z : Fin e → ℂ => a + c • z) z :=
      AnalyticAt.comp ((hψ j).2 (a + c • z) ⟨h1, hj⟩) hTa
    have hmem : ((A.chart j ∘ ψ.symm) ∘ fun z : Fin e → ℂ => a + c • z) z ∈
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' O :=
      ⟨(A.chart j).map_source hj, by
        simpa [Set.mem_preimage, (A.chart j).left_inv hj] using h2⟩
    have hOo := (A.chart j).isOpen_inter_preimage_symm hO
    have hφ : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm)
        (((A.chart j ∘ ψ.symm) ∘ fun z : Fin e → ℂ => a + c • z) z) :=
      ((hf j).contDiffAt (hOo.mem_nhds hmem)).of_le (WithTop.coe_le_coe.mpr le_top)
    have hev : (fun z => f (ψ.symm (a + c • z))) =ᶠ[𝓝 z]
        (f ∘ (A.chart j).symm) ∘ ((A.chart j ∘ ψ.symm) ∘ fun z : Fin e → ℂ => a + c • z) := by
      have hcT : ContinuousAt (fun z => ψ.symm (a + c • z)) z :=
        ContinuousAt.comp (f := fun z : Fin e → ℂ => a + c • z) (ψ.continuousAt_symm h1) hTa.continuousAt
      filter_upwards [hcT.eventually ((A.chart j).open_source.mem_nhds hj)] with z' hz'
      simp [(A.chart j).left_inv hz']
    refine ⟨?_, fun w => ?_⟩
    · have hR : AnalyticAt ℝ ((A.chart j ∘ ψ.symm) ∘ fun z : Fin e → ℂ => a + c • z) z :=
        hτa.restrictScalars
      exact (hφ.comp z hR.contDiffAt).congr_of_eventuallyEq hev
    · rw [levi_congr hev, levi_comp w hτa hφ]
      exact hl j _ hmem _
  refine ⟨fun z hz => (key z hz).1.continuousAt.continuousWithinAt, ?_⟩
  exact (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm e V _ hV
    (fun z hz => (key z hz).1.contDiffWithinAt)).2
      ⟨fun z hz => (key z hz).1.contDiffWithinAt, fun z hz w => (key z hz).2 w⟩

theorem log_le_growth {r Q D l : ℝ} (hr : 0 < r) (h : r ≤ Q + D * l) (hl : 0 ≤ l) :
    Real.log r ≤ (|Real.log (|Q| + |D| + 1)| + 1) * Real.log (Real.exp 1 + l) := by
  set K : ℝ := |Q| + |D| + 1 with hK
  have hK1 : 1 ≤ K := by have := abs_nonneg Q; have := abs_nonneg D; linarith
  have hK0 : 0 < K := by linarith
  have he1 : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hpos : 0 < Real.exp 1 + l := by linarith
  have hle : r ≤ K * (Real.exp 1 + l) := by
    have h1 : Q ≤ K := by have := le_abs_self Q; have := abs_nonneg D; linarith
    have h2 : D ≤ K := by have := le_abs_self D; have := abs_nonneg Q; linarith
    have h3 : K ≤ K * Real.exp 1 := le_mul_of_one_le_right hK0.le he1
    have h4 : D * l ≤ K * l := mul_le_mul_of_nonneg_right h2 hl
    nlinarith
  have hlog := Real.log_le_log hr hle
  rw [Real.log_mul hK0.ne' hpos.ne'] at hlog
  have hL : 1 ≤ Real.log (Real.exp 1 + l) := by
    have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hl (a := Real.exp 1))
    rwa [Real.log_exp] at this
  have h5 : Real.log K ≤ |Real.log K| * Real.log (Real.exp 1 + l) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hL)
  nlinarith

theorem localBound {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {nb : ℕ} (m : Fin nb → ℕ) (W : Fin nb → Set X) (hL : IsPotential A L)
    (hS : IsSection A L s) (hSNC : IsSNC A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0)
    (th : LocPot X) (u : X → ℝ) (C₁ : ℝ) (hth : IsPotential A th) (hu : A.SmoothOn (bdry s)ᶜ u)
    (hpsh : IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u))
    (hC : ∀ y ∉ bdry s, |u y| ≤ C₁ * Real.log (rW L s y)) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ B : ℝ, ∀ y ∈ V, y ∉ bdry s → u y ≤ B := by
  classical
  obtain ⟨ψ, hcompat, hxψ, hψU, σ, -, -, g, hg, hg0, hprod⟩ := hSNC x
  set a : Fin e → ℂ := ψ x with ha
  let tm : Fin nb → (Fin e → ℂ) → ℂ := fun k w => match σ k with
    | some i => w i ^ m k
    | none => 1
  have hprod' : ∀ y ∈ ψ.source, s x y = g y * ∏ k, tm k (ψ y) := hprod
  let S' : Finset (Fin e) := Finset.univ.filter fun i => a i = 0 ∧ ∃ k, σ k = some i ∧ m k ≠ 0
  have hat : a ∈ ψ.target := ψ.map_source hxψ
  have hsa : ψ.symm a = x := ψ.left_inv hxψ
  have hnb : ∀ᶠ w in 𝓝 a, (w ∈ ψ.target ∧ ψ.symm w ∈ th.U x) ∧
      ∀ i, a i ≠ 0 → ‖a i‖ / 2 < ‖w i‖ := by
    refine Filter.Eventually.and ?_ (eventually_all.2 fun i => ?_)
    · exact (ψ.isOpen_inter_preimage_symm (th.isOpen_U x)).mem_nhds
        ⟨hat, by simpa [Set.mem_preimage, hsa] using th.mem_U x⟩
    · by_cases hi : a i = 0
      · exact Eventually.of_forall fun w h => absurd hi h
      · have hc : ContinuousAt (fun w : Fin e → ℂ => ‖w i‖) a := (continuous_apply i).norm.continuousAt
        have h2 : ‖a i‖ / 2 < ‖a i‖ := half_lt_self (norm_pos_iff.2 hi)
        filter_upwards [hc.eventually (lt_mem_nhds h2)] with w hw _ using hw
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hnb
  have hst : ∀ w ∈ Metric.closedBall a ρ, ψ.symm w ∈ ψ.source := fun w hw =>
    ψ.map_target (hball hw).1.1
  have bd : ∀ f : X → ℝ, (∀ w ∈ Metric.closedBall a ρ, ContinuousAt f (ψ.symm w)) →
      ∃ M, ∀ w ∈ Metric.closedBall a ρ, |f (ψ.symm w)| ≤ M := by
    intro f hf
    have hc : ContinuousOn (fun w => f (ψ.symm w)) (Metric.closedBall a ρ) := fun w hw =>
      (ContinuousAt.comp (f := ψ.symm) (hf w hw) (ψ.continuousAt_symm (hball hw).1.1)).continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_closedBall a ρ).exists_bound_of_continuousOn hc
    exact ⟨M, fun w hw => by simpa [Real.norm_eq_abs] using hM w hw⟩
  obtain ⟨M₁, hM₁⟩ := bd (th.φ x) fun w hw =>
    LeviFormBoundaryTopology.continuousAt_of_smoothOn A (th.isOpen_U x) (hth.1 x) (hball hw).1.2
  obtain ⟨M₂, hM₂⟩ := bd (L.φ x) fun w hw =>
    LeviFormBoundaryTopology.continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (hψU (hst w hw))
  obtain ⟨M₃, hM₃⟩ := bd (fun y => Real.log ‖g y‖) fun w hw =>
    (LeviFormBoundaryTopology.continuousAt_of_holoOn A hg (hst w hw)).norm.log
      (norm_ne_zero_iff.2 (hg0 _ (hst w hw)))
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hwz : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1, a + (ρ : ℂ) • z ∈ Metric.closedBall a ρ := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa using hz
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg z]
  have hl0 : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1, ∀ i, 0 ≤ Real.log ‖z i‖⁻¹ := by
    intro z hz i
    have hz1 : ‖z‖ < 1 := by simpa using hz
    rw [Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm z i).trans hz1.le))
  have hl1 : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1, 0 ≤ ∑ i ∈ S', Real.log ‖z i‖⁻¹ := fun z hz =>
    Finset.sum_nonneg fun i _ => hl0 z hz i
  have hk : ∀ k, ∃ B : ℝ, ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1 \ ReciprocityTheory.AnForm.A.coordDiv S',
      tm k (a + (ρ : ℂ) • z) ≠ 0 ∧
        -B - m k * ∑ i ∈ S', Real.log ‖z i‖⁻¹ ≤ Real.log ‖tm k (a + (ρ : ℂ) • z)‖ := by
    intro k
    have hmn : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1, 0 ≤ (m k : ℝ) * ∑ i ∈ S', Real.log ‖z i‖⁻¹ :=
      fun z hz => mul_nonneg (Nat.cast_nonneg _) (hl1 z hz)
    rcases hσ : σ k with _ | i
    · refine ⟨0, fun z hz => ?_⟩
      have h1 : tm k (a + (ρ : ℂ) • z) = 1 := by simp [tm, hσ]
      rw [h1]
      have := hmn z hz.1
      simp only [ne_eq, one_ne_zero, not_false_eq_true, norm_one, Real.log_one, true_and]
      linarith
    · have htm : ∀ w, tm k w = w i ^ m k := fun w => by simp [tm, hσ]
      by_cases hm : m k = 0
      · refine ⟨0, fun z hz => ?_⟩
        rw [htm, hm]
        simp
      by_cases hai : a i = 0
      · have hiS : i ∈ S' := by
          simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hai, k, hσ, hm⟩
        refine ⟨|(m k : ℝ) * Real.log ρ|, fun z hz => ?_⟩
        have hz0 : z i ≠ 0 := fun h => hz.2 ⟨i, hiS, h⟩
        have hw : (a + (ρ : ℂ) • z) i = (ρ : ℂ) * z i := by simp [hai]
        refine ⟨by rw [htm, hw]; exact pow_ne_zero _ (mul_ne_zero hρc hz0), ?_⟩
        rw [htm, norm_pow, Real.log_pow, hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le,
          Real.log_mul hρ.ne' (norm_ne_zero_iff.2 hz0)]
        have h1 : Real.log ‖z i‖⁻¹ ≤ ∑ i ∈ S', Real.log ‖z i‖⁻¹ :=
          Finset.single_le_sum (f := fun i => Real.log ‖z i‖⁻¹) (fun i _ => hl0 z hz.1 i) hiS
        rw [Real.log_inv] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (m k))
        have h3 := neg_abs_le ((m k : ℝ) * Real.log ρ)
        nlinarith
      · refine ⟨|(m k : ℝ) * Real.log (‖a i‖ / 2)|, fun z hz => ?_⟩
        have h2 := (hball (hwz z hz.1)).2 i hai
        have hp : 0 < ‖a i‖ / 2 := half_pos (norm_pos_iff.2 hai)
        refine ⟨by rw [htm]; exact pow_ne_zero _ (norm_pos_iff.1 (hp.trans h2)), ?_⟩
        rw [htm, norm_pow, Real.log_pow]
        have h3 := Real.log_le_log hp h2.le
        have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (α := ℝ) (m k))
        have h5 := neg_abs_le ((m k : ℝ) * Real.log (‖a i‖ / 2))
        have h6 := hmn z hz.1
        linarith
  choose Bk hBk using hk
  have hD : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1 \ ReciprocityTheory.AnForm.A.coordDiv S',
      ψ.symm (a + (ρ : ℂ) • z) ∈ ψ.source ∧ s x (ψ.symm (a + (ρ : ℂ) • z)) ≠ 0 ∧
      ‖s x (ψ.symm (a + (ρ : ℂ) • z))‖ =
        ‖g (ψ.symm (a + (ρ : ℂ) • z))‖ * ∏ k, ‖tm k (a + (ρ : ℂ) • z)‖ := by
    intro z hz
    have h1 := hst _ (hwz z hz.1)
    have h2 : s x (ψ.symm (a + (ρ : ℂ) • z)) = g (ψ.symm (a + (ρ : ℂ) • z)) *
        ∏ k, tm k (a + (ρ : ℂ) • z) := by
      rw [hprod' _ h1, ψ.right_inv (hball (hwz z hz.1)).1.1]
    refine ⟨h1, ?_, ?_⟩
    · rw [h2]
      exact mul_ne_zero (hg0 _ h1) (Finset.prod_ne_zero_iff.2 fun k _ => (hBk k z hz).1)
    · rw [h2, norm_mul, norm_prod]
  have hoff : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1 \ ReciprocityTheory.AnForm.A.coordDiv S',
      ψ.symm (a + (ρ : ℂ) • z) ∉ bdry s := fun z hz h =>
    (hD z hz).2.1 ((LeviFormBoundaryTopology.bdry_iff hS (hψU (hD z hz).1)).1 h)
  have hr : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1 \ ReciprocityTheory.AnForm.A.coordDiv S',
      rW L s (ψ.symm (a + (ρ : ℂ) • z)) ≤ (Real.exp 1 + 2 * M₃ + 2 * M₂ + 2 * ∑ k, Bk k) +
        (2 * ∑ k, (m k : ℝ)) * ∑ i ∈ S', Real.log ‖z i‖⁻¹ := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hD z hz
    have hw := hwz z hz.1
    have hgz : ‖g (ψ.symm (a + (ρ : ℂ) • z))‖ ≠ 0 := norm_ne_zero_iff.2 (hg0 _ h1)
    have htz : ∀ k ∈ Finset.univ, ‖tm k (a + (ρ : ℂ) • z)‖ ≠ 0 := fun k _ =>
      norm_ne_zero_iff.2 (hBk k z hz).1
    have hlog : Real.log ‖s x (ψ.symm (a + (ρ : ℂ) • z))‖ =
        Real.log ‖g (ψ.symm (a + (ρ : ℂ) • z))‖ + ∑ k, Real.log ‖tm k (a + (ρ : ℂ) • z)‖ := by
      rw [h3, Real.log_mul hgz (Finset.prod_ne_zero_iff.2 htz), Real.log_prod htz]
    have hsum : ∑ k, (-Bk k - m k * ∑ i ∈ S', Real.log ‖z i‖⁻¹) ≤
        ∑ k, Real.log ‖tm k (a + (ρ : ℂ) • z)‖ :=
      Finset.sum_le_sum fun k _ => (hBk k z hz).2
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul] at hsum
    have b2 := (abs_le.1 (hM₂ _ hw)).2
    have b3 := (abs_le.1 (hM₃ _ hw)).1
    simp only [rW]
    rw [logNormSecLocal A L s x _ hS (hψU h1) h2, hlog]
    linarith
  set Cc : ℝ := |M₁| + |C₁| * (|Real.log (|Real.exp 1 + 2 * M₃ + 2 * M₂ + 2 * ∑ k, Bk k| +
    |2 * ∑ k, (m k : ℝ)| + 1)| + 1) with hCc
  have hFb : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1 \ ReciprocityTheory.AnForm.A.coordDiv S',
      (fun y => th.φ x y + u y) (ψ.symm (a + (ρ : ℂ) • z)) ≤
        Cc * Real.log (Real.exp 1 + ∑ i ∈ S', Real.log ‖z i‖⁻¹) := by
    intro z hz
    have hy := hoff z hz
    have he1 : 1 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hrge := rW_ge L s hn (ψ.symm (a + (ρ : ℂ) • z))
    have hrpos : 0 < rW L s (ψ.symm (a + (ρ : ℂ) • z)) := by linarith
    have hlogr : 0 ≤ Real.log (rW L s (ψ.symm (a + (ρ : ℂ) • z))) :=
      Real.log_nonneg (by linarith)
    have hg1 := log_le_growth hrpos (hr z hz) (hl1 z hz.1)
    have hL1 : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S', Real.log ‖z i‖⁻¹) := by
      have := Real.log_le_log (Real.exp_pos 1)
        (le_add_of_nonneg_right (hl1 z hz.1) (a := Real.exp 1))
      rwa [Real.log_exp] at this
    have hu1 : u (ψ.symm (a + (ρ : ℂ) • z)) ≤
        |C₁| * Real.log (rW L s (ψ.symm (a + (ρ : ℂ) • z))) :=
      (le_abs_self _).trans ((hC _ hy).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C₁) hlogr))
    have hu2 := hu1.trans (mul_le_mul_of_nonneg_left hg1 (abs_nonneg C₁))
    have hth1 : th.φ x (ψ.symm (a + (ρ : ℂ) • z)) ≤
        |M₁| * Real.log (Real.exp 1 + ∑ i ∈ S', Real.log ‖z i‖⁻¹) :=
      ((le_abs_self _).trans ((hM₁ _ (hwz z hz.1)).trans (le_abs_self _))).trans
        (le_mul_of_one_le_right (abs_nonneg _) hL1)
    show th.φ x _ + u _ ≤ _
    rw [hCc, add_mul, mul_assoc]
    linarith
  have hclosed : IsClosed (ReciprocityTheory.AnForm.A.coordDiv S') := by
    have : ReciprocityTheory.AnForm.A.coordDiv S' = ⋃ i ∈ S', {z : Fin e → ℂ | z i = 0} := by
      ext z
      simp [ReciprocityTheory.AnForm.A.coordDiv]
    rw [this]
    exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const
  have hVo : IsOpen (Metric.ball (0 : Fin e → ℂ) 1 \ ReciprocityTheory.AnForm.A.coordDiv S') :=
    Metric.isOpen_ball.sdiff hclosed
  have hpull := pshPull A ψ hcompat (O := th.U x ∩ (bdry s)ᶜ)
    ((th.isOpen_U x).inter (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl)
    (f := fun y => th.φ x y + u y)
    (fun j => ((hth.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩).add
      ((hu j).mono fun y hy => ⟨hy.1, hy.2.2⟩))
    (fun j y hy w => hpsh x j y ⟨hy.1, ⟨hy.2.1, trivial⟩, hy.2.2⟩ w)
    a (ρ : ℂ) hVo
    (fun z hz => ⟨(hball (hwz z hz.1)).1.1, (hball (hwz z hz.1)).1.2, hoff z hz⟩)
  obtain ⟨hbd, -⟩ := ReciprocityTheory.AnForm.A.pshExtension_thm e S' (Metric.ball 0 1) _ Cc Metric.isOpen_ball
    subset_rfl hpull.1 hpull.2 hFb
  obtain ⟨Bm, hBm⟩ := hbd (Metric.closedBall 0 (1 / 2)) (isCompact_closedBall _ _)
    (Metric.closedBall_subset_ball (by norm_num))
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball a (ρ / 2), ψ.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hxψ, Metric.mem_ball_self (half_pos hρ)⟩, Bm + M₁, ?_⟩
  rintro y ⟨hy1, hy2⟩ hyb
  have hy2' : ‖ψ y - a‖ < ρ / 2 := by
    have : dist (ψ y) a < ρ / 2 := hy2
    rwa [dist_eq_norm] at this
  have hwy : a + (ρ : ℂ) • (((ρ : ℂ)⁻¹) • (ψ y - a)) = ψ y := by
    rw [smul_smul, mul_inv_cancel₀ hρc, one_smul, add_sub_cancel]
  have hzn : ‖((ρ : ℂ)⁻¹) • (ψ y - a)‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le, inv_mul_le_iff₀ hρ]
    linarith
  have hzc : ((ρ : ℂ)⁻¹) • (ψ y - a) ∉ ReciprocityTheory.AnForm.A.coordDiv S' := by
    rintro ⟨i, hi, hzi⟩
    simp only [S', Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hai, k, hσ, hm⟩ := hi
    have hyi : ψ y i = 0 := by
      have := congrFun hwy i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this hzi
      rw [← this, hzi, hai]
      simp
    apply hyb
    refine (LeviFormBoundaryTopology.bdry_iff hS (hψU hy1)).2 ?_
    rw [hprod' y hy1]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ k) ?_)
    simp [tm, hσ, hyi, hm]
  have h1 := hBm ⟨_, ⟨Metric.mem_closedBall.2 (by simpa using hzn), hzc⟩, rfl⟩
  simp only [hwy, ψ.left_inv hy1] at h1
  have h2 := hM₁ (ψ y) (Metric.mem_closedBall.2 (by
    rw [dist_eq_norm]; linarith))
  rw [ψ.left_inv hy1] at h2
  linarith [neg_abs_le (th.φ x y), (abs_le.1 h2).1]

theorem isSingWeight_of_logGrowth : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : LocPot X) (u : X → ℝ) (C₁ : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → (∀ y ∉ bdry s, |u y| ≤ C₁ * Real.log (rW L s y)) → ∃ C₅, IsSingWeight A L s th u C₅ := by
  intro e X _ _ _ A L s nb m W hL hS hSNC hn th u C₁ hth hu hpsh hC
  choose V hVo hxV B hB using localBound A L s m W hL hS hSNC hn th u C₁ hth hu hpsh hC
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover V fun x => (hVo x).mem_nhds (hxV x)
  refine ⟨|C₁| + ∑ x ∈ t, |B x|, hth, hu, hpsh, fun y hy => ?_⟩
  have hS0 : 0 ≤ ∑ x ∈ t, |B x| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have he1 : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hlogr : 0 ≤ Real.log (rW L s y) := Real.log_nonneg (by linarith [rW_ge L s hn y])
  constructor
  · have h1 := hC y hy
    have h2 : C₁ * Real.log (rW L s y) ≤ (|C₁| + ∑ x ∈ t, |B x|) * Real.log (rW L s y) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₁]) hlogr
    linarith [neg_abs_le (u y)]
  · have hy' : y ∈ (⊤ : Set X) := trivial
    rw [← ht] at hy'
    simp only [Set.mem_iUnion, exists_prop] at hy'
    obtain ⟨x, hx, hyx⟩ := hy'
    have h1 := hB x y hyx hy
    have h2 : |B x| ≤ ∑ x ∈ t, |B x| :=
      Finset.single_le_sum (f := fun x => |B x|) (fun _ _ => abs_nonneg _) hx
    linarith [le_abs_self (B x), abs_nonneg C₁]

end GlobalTheory.CompanionTheory.Ar.PB
