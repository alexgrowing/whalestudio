import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompareStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrArch

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_torus (A : HermLine ι) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {w : (Σ k, ι k) → ℂ}
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * w p) = ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ + Real.log (A.h w) := by
  have h0 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [A.smul c w hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (h0 k))
    (A.pos w hw).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (h0 k))]
  simp only [Real.log_zpow]

theorem log_sub_of_sameOrbit {A B : HermLine ι} (hAB : A.a = B.a) {z w : (Σ k, ι k) → ℂ}
    (h : SameOrbit z w) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h w) - Real.log (B.h w) := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [log_h_torus A hc hw, log_h_torus B hc hw, hAB]
  ring

theorem log_add_sum_of_sameOrbit {α : Type} (T : Finset α) {A : HermLine ι} (B : α → HermLine ι)
    (hA : A.a = -∑ j ∈ T, (B j).a) {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z) =
      Real.log (A.h w) + ∑ j ∈ T, Real.log ((B j).h w) := by
  obtain ⟨c, hc, rfl⟩ := h
  simp only [log_h_torus _ hc hw, Finset.sum_add_distrib]
  have h1 : ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ =
      -∑ j ∈ T, ∑ k, ((B j).a k : ℝ) * Real.log ‖c k‖ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA, Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, neg_mul, Finset.sum_mul]
  rw [h1]
  ring

end Lines

theorem defect_eq_regWeight_add_bracket :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (x : o.Re.R.X) (x' : o₀.Re.R.X) (w₁ : (Σ k, M.ι k) → ℂ) (w₂ : (Σ k, R.ι k) → ℂ) (v : RootIx D → ℝ) (t : ℝ), 0 < t → t ≤ Sys.t₀ → w₁ ∈ mcPts M.P → w₂ ∈ mcPts R.P → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w₁ → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') w₂ → o.Re.π x = o₀.Re.π x' → o.Re.π x ∈ Sys.open' → (∀ r, 0 < v r ∧ v r * (o₀.sing r).h w₂ = (o.sing r).h w₁) → ∀ (τ : CMType H) (p : Fin (D.p + D.q)), -∑ k ∈ Finset.Iic p, (Real.log ((M.x t (τ, k)).h w₁) - Real.log ((R.x 1 (τ, k)).h w₂) - Real.log (v (τ, k))) = Sys.phT (some (τ, p)) t (o.Re.π x) + (Real.log ((o₀.Re.ref (some (τ, p))).h w₂) + ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)) := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ x x' w₁ w₂ v t ht0 htle hw₁ hw₂ hx hx' hπ hop hv τ p
  have hop₀ : o₀.Re.π x' ∈ Sys.open' := hπ ▸ hop

  have hreg := o.fund_reg τ p t ht0 htle w₁ hw₁
  have hline := o.Re.line_eq (some (τ, p)) t ht0 htle x
  have hsc := log_sub_of_sameOrbit (o.Re.line_deg (some (τ, p)) t) hx hw₁.1

  have hs := o.fund_sing τ p x hop
  have hs₀ := o₀.fund_sing τ p x' hop₀
  have hdeg : ∀ (N : Top.RootModel (CMType H) (D.p + D.q)) (S' : Finset ℕ) (Fx' : FixedData Y Sys)
      (q : RootOrigin Y S' N Fx'),
      (q.Re.ref (some (τ, p))).a = -∑ k ∈ Finset.Iic p, (q.sing (τ, k)).a := by
    intro N S' Fx' q
    rw [q.fund_deg τ p]
    simp only [q.sing_deg]
  have hb := log_add_sum_of_sameOrbit (Finset.Iic p) (fun k => o.sing (τ, k)) (hdeg _ _ _ o) hx hw₁.1
  have hb₀ := log_add_sum_of_sameOrbit (Finset.Iic p) (fun k => o₀.sing (τ, k)) (hdeg _ _ _ o₀) hx' hw₂.1

  have hsum : ∑ k ∈ Finset.Iic p, Real.log ((o.sing (τ, k)).h w₁) =
      ∑ k ∈ Finset.Iic p, Real.log (v (τ, k)) + ∑ k ∈ Finset.Iic p, Real.log ((o₀.sing (τ, k)).h w₂) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨h0, h1⟩ := hv (τ, k)
    rw [← h1, Real.log_mul h0.ne' ((o₀.sing (τ, k)).pos w₂ hw₂.1).ne']
  rw [hπ] at hs hline
  simp only [Finset.sum_sub_distrib]
  rw [hπ]
  linarith

end GlobalTheory.CompanionTheory.Ar.OrArch
