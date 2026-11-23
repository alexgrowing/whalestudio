import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsForallNeZeroOfCountableAnalytic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowEval

noncomputable def absConv (u : ℂ) : Subring (PowerSeries ℂ) where
  carrier := {Φ | Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖}
  zero_mem' := by simp
  one_mem' := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [PowerSeries.coeff_one, Finset.notMem_singleton.1 hn]
  add_mem' := by
    intro f g hf hg
    refine (Summable.add hf hg).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add, add_mul]
    exact norm_add_le _ _
  neg_mem' := by
    intro f hf
    simpa [map_neg, neg_mul, norm_neg] using hf
  mul_mem' := by
    intro f g hf hg
    have e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
      rw [PowerSeries.coeff_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun kl h => ?_
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
      ring
    show Summable fun n => ‖PowerSeries.coeff n (f * g) * u ^ n‖
    simp only [e]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => PowerSeries.coeff n f * u ^ n) (g := fun n => PowerSeries.coeff n g * u ^ n) hf hg

noncomputable def evalAt (u : ℂ) : absConv u →+* ℂ where
  toFun Φ := ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n
  map_one' := by
    rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
    simp
  map_zero' := by simp
  map_add' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    simp only [Subring.coe_add, map_add, add_mul]
    exact hf.of_norm.tsum_add hg.of_norm
  map_mul' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    refine tsum_congr fun n => ?_
    simp only [Subring.coe_mul]
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl h => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
    ring

theorem countable_closure {A : Type} [CommRing A] (S : Set A) (hS : S.Countable) :
    Countable (Subring.closure S) := by
  haveI : Countable S := hS.to_subtype
  haveI : Countable (MvPolynomial S ℤ) :=
    (MvPolynomial.basisMonomials S ℤ).repr.injective.countable
  let φ : MvPolynomial S ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) Subtype.val
  have hle : Subring.closure S ≤ φ.range := Subring.closure_le.2 fun s hs =>
    ⟨MvPolynomial.X ⟨s, hs⟩, by simp [φ]⟩
  have hc : (φ.range : Set A).Countable := by
    rw [RingHom.coe_range]; exact Set.countable_range _
  exact (hc.mono hle).to_subtype

theorem radius_ge (ε : ℝ) (Φ : PowerSeries ℂ)
    (h : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) :
    ENNReal.ofReal ε ≤ (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrε : (r : ℝ) < ε := by
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 hr
  refine FormalMultilinearSeries.le_radius_of_summable _ ?_
  have hs := h (r : ℂ) (by exact_mod_cast hr0) (by simpa using hrε)
  refine hs.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]
  simp

end GlobalTheory.PowEval

open GlobalTheory.PowEval in

theorem GlobalTheory.exists_injective_evalAt_closure : ∀ (ε : ℝ) (S : Set (PowerSeries ℂ)), 0 < ε → S.Countable → (∀ Φ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) → ∃ (u : ℂ) (i : Subring.closure S →+* ℂ), u ≠ 0 ∧ ‖u‖ < ε ∧ Function.Injective i ∧ ∀ Φ : Subring.closure S, i Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n := by
  intro ε S hε hS h
  haveI : Countable (Subring.closure S) := countable_closure S hS
  let p : PowerSeries ℂ → FormalMultilinearSeries ℂ ℂ ℂ := fun Φ =>
    FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ
  have hsum : ∀ (Φ : PowerSeries ℂ) (u : ℂ), (p Φ).sum u = ∑' n, PowerSeries.coeff n Φ * u ^ n := by
    intro Φ u
    show FormalMultilinearSeries.ofScalarsSum _ u = _
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp [smul_eq_mul]
  have hcl : ∀ Φ ∈ Subring.closure S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖ := by
    intro Φ hΦ u hu0 hu
    have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hu
    exact hle hΦ
  have hrad : ∀ Φ ∈ Subring.closure S, ENNReal.ofReal ε ≤ (p Φ).radius := fun Φ hΦ =>
    radius_ge ε Φ (hcl Φ hΦ)
  have hpos : ∀ Φ ∈ Subring.closure S, 0 < (p Φ).radius := fun Φ hΦ =>
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) (hrad Φ hΦ)
  have hball : ∀ Φ ∈ Subring.closure S, Metric.ball (0 : ℂ) ε ⊆ EMetric.ball 0 (p Φ).radius := by
    intro Φ hΦ
    rw [← Metric.emetric_ball]
    exact EMetric.ball_subset_ball (hrad Φ hΦ)
  let J := Option {Φ : Subring.closure S // Φ ≠ 0}
  let f : J → ℂ → ℂ := fun i => match i with
    | none => id
    | some Φ => (p (Φ.1 : PowerSeries ℂ)).sum
  have han : ∀ i, AnalyticOnNhd ℂ (f i) (Metric.ball 0 ε) := by
    intro i
    cases i with
    | none => exact analyticOnNhd_id
    | some Φ =>
      exact ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).analyticOnNhd.mono (hball _ Φ.1.2)
  have hnz : ∀ i, ∃ x ∈ Metric.ball (0 : ℂ) ε, f i x ≠ 0 := by
    intro i
    cases i with
    | none =>
      refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      · show ((ε / 2 : ℝ) : ℂ) ≠ 0
        exact_mod_cast (by linarith : ε / 2 ≠ 0)
    | some Φ =>
      by_contra hcon
      push_neg at hcon
      have hev : (p (Φ.1 : PowerSeries ℂ)).sum =ᶠ[nhds 0] 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with y hy
        exact hcon y hy
      have h0 := ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).hasFPowerSeriesAt.eq_zero_of_eventually hev
      apply Φ.2
      apply Subtype.ext
      ext n
      have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n) h0
      simpa using (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := fun n => PowerSeries.coeff n (Φ.1 : PowerSeries ℂ)) n).1 this
  obtain ⟨u, hu, hx⟩ := GlobalTheory.exists_forall_ne_zero_of_countable_analytic ℂ (Metric.ball 0 ε)
    Metric.isOpen_ball (convex_ball 0 ε).isPreconnected (Metric.nonempty_ball.2 hε) J f han hnz
  have hu0 : u ≠ 0 := hx none
  have hun : ‖u‖ < ε := mem_ball_zero_iff.1 hu
  have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hun
  let i : Subring.closure S →+* ℂ := (evalAt u).comp (Subring.inclusion hle)
  refine ⟨u, i, hu0, hun, ?_, fun Φ => rfl⟩
  refine (injective_iff_map_eq_zero i).2 fun Φ hΦ => ?_
  by_contra hne
  apply hx (some ⟨Φ, hne⟩)
  show (p (Φ : PowerSeries ℂ)).sum u = 0
  rw [hsum]
  exact hΦ
