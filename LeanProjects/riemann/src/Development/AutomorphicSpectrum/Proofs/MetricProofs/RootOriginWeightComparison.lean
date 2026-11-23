import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

theorem sum_neg_mul_eq_sum_fundCo {Ψ : Type} [Fintype Ψ] {N : ℕ} (f : Ψ → Fin N → ℝ) (B R : Ψ × Fin N → ℝ)
    (h : ∀ τ i, R (τ, i) = -∑ k ∈ Finset.Iic i, B (τ, k)) :
    ∑ r : Ψ × Fin N, -f r.1 r.2 * B r = ∑ r : Ψ × Fin N, fundCo (f r.1) r.2 * R r := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e := sum_fundCo_mul_sum_Iic (f τ) fun k => B (τ, k)
  simp only [h, mul_neg, Finset.sum_neg_distrib, neg_mul]
  rw [e]

theorem weight_sub_log_sing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' : Option (RootIx D) → ℤ) (s : ℝ) (x : Or.Re.R.X), (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → scale s ≤ Sys.t₀ → Or.Re.π x ∈ Sys.open' → RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) - Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) = s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) - s * ∑ r : RootIx D, fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) + ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Sys.phT (some r) (scale s) (Or.Re.π x) - ∑ r : RootIx D, fundCo (lam r.1) r.2 * Sys.ph (some r) (Or.Re.π x) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' s x hn ht hop
  have hw := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have ht0 : 0 < scale s := Real.exp_pos _
  have hreg : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h (Or.Re.R.lift x x)) +
      Sys.phT (some (τ, i)) (scale s) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((RM.x (scale s) (τ, k)).h (Or.Re.R.lift x x)) := fun τ i => by
    rw [← Or.fund_reg τ i (scale s) ht0 ht _ hw, Or.Re.line_eq (some (τ, i)) (scale s) ht0 ht x]
  have hsing : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h (Or.Re.R.lift x x)) +
      Sys.ph (some (τ, i)) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((Or.sing (τ, k)).h (Or.Re.R.lift x x)) :=
    fun τ i => Or.fund_sing τ i x hop
  have e1 := sum_neg_mul_eq_sum_fundCo (lam - s • nu)
    (fun r => Real.log ((RM.x (scale s) r).h (Or.Re.R.lift x x)))
    (fun r => Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) +
      Sys.phT (some r) (scale s) (Or.Re.π x)) hreg
  have e2 := sum_neg_mul_eq_sum_fundCo lam
    (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x)))
    (fun r => Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) +
      Sys.ph (some r) (Or.Re.π x)) hsing
  have hlog : Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) =
      ∑ r : RootIx D, -lam r.1 r.2 * Real.log ((Or.sing r).h (Or.Re.R.lift x x)) := by
    rw [Real.log_prod fun r _ => zpow_ne_zero _ ((Or.sing r).pos _ hw.1).ne']
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.log_zpow, hn (some r)]
    rfl
  have hwt : RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) =
      s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) +
        ∑ r : RootIx D, -(lam - s • nu) r.1 r.2 * Real.log ((RM.x (scale s) r).h (Or.Re.R.lift x x)) := by
    unfold RootModel.weight
    rw [Fintype.sum_option]
    rfl
  rw [hwt, hlog, e1, e2]
  have hco : ∀ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 = fundCo (lam r.1) r.2 - s * fundCo (nu r.1) r.2 := by
    intro r
    have : (lam - s • nu) r.1 = lam r.1 - s • nu r.1 := rfl
    rw [this, fundCo_sub, fundCo_smul]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  have hρ : ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) =
      ∑ r : RootIx D, fundCo (lam r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) -
        ∑ r : RootIx D, s * (fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hco]
    ring
  rw [hρ]
  ring

end GlobalTheory.CompanionTheory.Ar.Small.Fund
