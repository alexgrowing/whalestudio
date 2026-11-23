import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace AnMono

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_isPosPot (A : FinHolAtlas e X) (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

theorem log_inv_ge {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / t) ∧ 0 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  exact ⟨h1, Real.log_nonneg h1⟩

theorem quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_ge ht hte
  exact div_nonneg h2 (by linarith)

theorem epsT_mono {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    epsT C t ≤ epsT C' t := by
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (quot_nonneg ht hte)

theorem mul_epsT_mono {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    C * epsT C t ≤ C' * epsT C' t := by
  have hx := quot_nonneg ht hte
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

theorem exp_one_le_rW (L : LocPot X) (s : X → X → ℂ) (hs : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    Real.exp 1 ≤ rW L s y := by
  have := hs y
  unfold rW
  linarith

theorem one_le_log_rW (L : LocPot X) (s : X → X → ℂ) (hs : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    1 ≤ Real.log (rW L s y) := by
  have := Real.log_le_log (Real.exp_pos 1) (exp_one_le_rW L s hs y)
  rwa [Real.log_exp] at this

theorem isSingWeight_mono (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (th : LocPot X) (ph : X → ℝ) {C₅ C₅' : ℝ} (hC : C₅ ≤ C₅')
    (h : IsSingWeight A L s th ph C₅) : IsSingWeight A L s th ph C₅' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  obtain ⟨h5, h6⟩ := h4 y hy
  have hl := one_le_log_rW L s hs y
  constructor
  · nlinarith
  · linarith

theorem isRegFamily_enlarge (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X)
    (ph : X → ℝ) (phT : ℝ → X → ℝ) {C t₀ C' t₁ : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hs : ∀ y, logNormSec L s y ≤ 0)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀)
    (hte : t₁ ≤ Real.exp (-1)) : IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y =>
    (Real.exp_pos 1).le.trans (exp_one_le_rW L s hs y)
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-1) := htt.trans hte
  have hε := epsT_mono hCC ht hte'
  have hll := (log_inv_ge ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_,
    fun y hy => ?_, fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_mono hC (ht.trans_le htt') (ht'.trans hte)
    linarith

theorem continuous_of_smooth (A : FinHolAtlas e X) (u : X → ℝ) (h : A.Smooth u) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (u ∘ (A.chart j).symm) (A.chart j).target := by
    have := (h j).continuousOn
    simpa using this
  have hx : (A.chart j) x ∈ (A.chart j).target := (A.chart j).map_source hj
  have h2 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x) :=
    h1.continuousAt ((A.chart j).open_target.mem_nhds hx)
  have h3 : ContinuousAt (A.chart j) x := (A.chart j).continuousAt hj
  have h4 : ContinuousAt ((u ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp (g := u ∘ (A.chart j).symm) h2 h3
  refine h4.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem tendstoUniformlyOn_self {α β : Type*} [UniformSpace β] (f : α → β) (p : Filter ℝ)
    (K : Set α) : TendstoUniformlyOn (fun _ : ℝ => f) f p K := by
  intro v hv
  exact Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hv

theorem isRegFamilyC2_const (A : FinHolAtlas e X) (s : X → X → ℂ) (u : X → ℝ) :
    IsRegFamilyC2 A s u (fun _ => u) := fun j K _ _ =>
  ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _⟩

theorem isPsh_add_rsmul (A : FinHolAtlas e X) (Θ th : LocPot X) (u : X → ℝ) {ε : ℝ}
    (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th) (hu : A.Smooth u)
    (hε : 0 ≤ ε) (h : IsPsh A (th + LocPot.ofFun u)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε) := by
  refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th u hΘ hΘp hth hu hε ?_
  intro x j y hy w
  have hfun : (th + LocPot.ofFun u + Θ.rsmul 0).φ x ∘ (A.chart j).symm =
      (th + LocPot.ofFun u).φ x ∘ (A.chart j).symm := by
    funext z
    show th.φ x _ + u _ + 0 * Θ.φ x _ = th.φ x _ + u _
    ring
  rw [hfun]
  exact h x j y ⟨hy.1, hy.2.1⟩ w

theorem smooth_member [CompactSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ)
    (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hs : ∀ y, logNormSec L s y ≤ 0) (th : LocPot X)
    (u : X → ℝ) (hth : IsPotential A th) (hu : A.Smooth u) (hp : IsPsh A (th + LocPot.ofFun u)) :
    ∃ C₀, IsSingWeight A L s th u C₀ ∧
      IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧
        IsRegFamilyC2 A s u (fun _ => u) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_of_smooth A u hu).continuousOn
  have hb : ∀ y, |u y| ≤ |M| + 1 := fun y => by
    have := hM y (Set.mem_univ y)
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M]
  set C₀ : ℝ := |M| + 1 with hC₀
  have hC0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀, ⟨hth, fun j => (hu j).mono ?_, fun x j y hy w => ?_, fun y _ => ?_⟩, ?_,
    isRegFamilyC2_const A s u⟩
  · exact fun z hz => ⟨hz.1, Set.mem_univ _⟩
  · exact hp x j y ⟨hy.1, hy.2.1⟩ w
  · have hl := one_le_log_rW L s hs y
    have h := abs_le.1 (hb y)
    constructor
    · nlinarith
    · exact h.2
  · have he : 0 < Real.exp 1 := Real.exp_pos 1
    refine ⟨Real.exp_pos _, ?_, fun t ht htt => ?_⟩
    · exact Real.exp_lt_one_iff.2 (by linarith)
    have hl := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht htt
    have hq := GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg ht htt
    have hε : 0 ≤ epsT C₀ t := by
      rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
      exact mul_nonneg hC0 hq
    have hε' : ∀ t', 0 < t' → t' ≤ Real.exp (-Real.exp 1) → 0 ≤ C₀ * epsT C₀ t' := fun t' h0 h1 => by
      rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
      exact mul_nonneg hC0 (mul_nonneg hC0 (GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg h0 h1))
    have h3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨hu, fun y => (abs_le.1 (hb y)).2, fun y _ => le_rfl, fun y => ?_,
      isPsh_add_rsmul A Θ th u hΘ hΘp hth hu hε hp, fun y _ _ => by linarith, fun y _ => ?_,
      fun t' htt' ht' y => ?_⟩
    · have h := abs_le.1 (hb y)
      nlinarith [hl.2]
    · have := mul_nonneg hε (he.le.trans (exp_one_le_rW L s hs y))
      linarith
    · have := hε' t' (ht.trans_le htt') ht'
      linarith

end AnMono

theorem enlarging_constants_smooth_members :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
      (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X),
      IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
      IsPotential A Θ → IsPosPot A Θ →
      (∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight A L s th ph C₅ → IsSingWeight A L s th ph C₅') ∧
      (∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) →
        IsRegFamily A Θ L s th ph phT C t₀ → IsPotential A th →
        IsRegFamily A Θ L s th ph phT C' t₀') ∧
      ∀ th u, IsPotential A th → A.Smooth u → IsPsh A (th + LocPot.ofFun u) →
        ∃ C₀, IsSingWeight A L s th u C₀ ∧
          IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧
            IsRegFamilyC2 A s u (fun _ => u) := by
  intro e X _ _ _ A Θ L s nb m W _ _ _ hs hΘ hΘpos
  have hΘp := AnMono.isPsh_of_isPosPot A Θ hΘpos
  refine ⟨fun th ph C₅ C₅' hC h => AnMono.isSingWeight_mono A L s hs th ph hC h,
    fun th ph phT C t₀ C' t₀' hC h0 h1 h2 hF hth => ?_,
    fun th u hth hu hp => AnMono.smooth_member A Θ L s hΘ hΘp hs th u hth hu hp⟩
  exact AnMono.isRegFamily_enlarge A Θ L s th ph phT hΘ hΘp hth hs hF hC h0 h1 h2

end GlobalTheory.CompanionTheory.Ar.PB
