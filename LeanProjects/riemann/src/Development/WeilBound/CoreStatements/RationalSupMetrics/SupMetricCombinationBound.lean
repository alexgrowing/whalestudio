import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace MultiProjectiveCoordinates

theorem supMet_pos_log {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {𝕜 : Type} [NormedField 𝕜]
    (z : (Σ k, ι k) → 𝕜) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (a : K → ℤ) :
    0 < supMet a z ∧ Real.log (supMet a z) = ∑ k, (a k : ℝ) * Real.log ‖fun i : ι k => z ⟨k, i⟩‖ := by
  have hN : ∀ k, 0 < ‖fun i : ι k => z ⟨k, i⟩‖ := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    refine norm_pos_iff.2 fun h => hi ?_
    exact congrFun h i
  refine ⟨Finset.prod_pos fun k _ => zpow_pos (hN k) _, ?_⟩
  unfold supMet
  rw [Real.log_prod fun k _ => (zpow_pos (hN k) _).ne']
  exact Finset.sum_congr rfl fun k _ => Real.log_zpow _ _

theorem supMet_combLine_le_pow_mul_prod : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (R : RootModel Ψ N) (lam : Wt Ψ N) (n' : Option (Ψ × Fin N) → ℤ) (p : ℕ) [Fact p.Prime] (z : (Σ k, R.ι k) → PadicAlgCl p) (rec : Ψ × Fin N → ℝ) (θ : ℝ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ j, (n' j : ℝ) = R.coef lam 0 j) → (∀ r, 0 < rec r) → (∀ r, |Real.log (supMet (R.xdeg r) z) - Real.log (rec r)| ≤ θ * Real.log p) → supMet (combLine (R.line 1) n').a z ≤ (p : ℝ) ^ (θ * l1 lam) * ∏ r, rec r ^ n' (some r) := by
  intro Ψ _ N R lam n' p _ z rc θ hz hn hrc hθ
  have hp : (0 : ℝ) < p := Nat.cast_pos.2 (Fact.out : p.Prime).pos
  have h0 : n' none = 0 := by
    have := hn none
    simp only [RootModel.coef, zero_div] at this
    exact_mod_cast this
  have h1 : ∀ r, (n' (some r) : ℝ) = -lam r.1 r.2 := fun r => hn (some r)
  have ha : ∀ k, (((combLine (R.line 1) n').a k : ℤ) : ℝ) = ∑ r, (n' (some r) : ℝ) * (R.xdeg r k : ℝ) := by
    intro k
    have : (combLine (R.line 1) n').a k = ∑ r, n' (some r) * R.xdeg r k := by
      show (∑ j, n' j • (R.line 1 j).a) k = _
      rw [Finset.sum_apply, Fintype.sum_option, h0]
      simp [RootModel.line, R.x_deg]
    rw [this]
    push_cast
    rfl
  obtain ⟨hpos, hlog⟩ := supMet_pos_log z hz (combLine (R.line 1) n').a
  have hlog2 : Real.log (supMet (combLine (R.line 1) n').a z) =
      ∑ r, (n' (some r) : ℝ) * Real.log (supMet (R.xdeg r) z) := by
    rw [hlog]
    simp only [ha, (supMet_pos_log z hz _).2, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => by ring
  have hprod : 0 < ∏ r, rc r ^ n' (some r) := Finset.prod_pos fun r _ => zpow_pos (hrc r) _
  have hpw : 0 < (p : ℝ) ^ (θ * l1 lam) := Real.rpow_pos_of_pos hp _
  rw [← Real.log_le_log_iff hpos (mul_pos hpw hprod), Real.log_mul hpw.ne' hprod.ne', Real.log_rpow hp,
    Real.log_prod fun r _ => (zpow_pos (hrc r) _).ne', hlog2]
  have hl : l1 lam = ∑ r : Ψ × Fin N, |lam r.1 r.2| := by
    unfold l1
    rw [Fintype.sum_prod_type]
  rw [hl, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [Real.log_zpow, h1 r]
  have h2 := hθ r
  have h3 : -lam r.1 r.2 * (Real.log (supMet (R.xdeg r) z) - Real.log (rc r)) ≤
      |lam r.1 r.2| * (θ * Real.log p) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  nlinarith [h3]

end MultiProjectiveCoordinates
