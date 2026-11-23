import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PunctShape

def factor (a : ℕ) (ρ : ℝ) (n : ℕ) (i : Fin n) : Set ℂ := {w | ‖w‖ < ρ ∧ (i.val < a → w ≠ 0)}

theorem punct_eq_pi (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    punct n a ρ = Set.pi Set.univ (factor a ρ n) := by
  ext z
  simp only [punct, factor, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
    mem_ball_zero_iff, pi_norm_lt_iff hρ]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨h1 i, h2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem isOpen_factor (n a : ℕ) (ρ : ℝ) (i : Fin n) : IsOpen (factor a ρ n i) := by
  by_cases h : i.val < a
  · have he : factor a ρ n i = Metric.ball 0 ρ ∩ {0}ᶜ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isOpen_ball.inter isOpen_compl_singleton
  · have he : factor a ρ n i = Metric.ball 0 ρ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isOpen_ball

theorem isConnected_factor (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (i : Fin n) :
    IsConnected (factor a ρ n i) := by
  by_cases h : i.val < a
  · have he : factor a ρ n i =
        (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (Set.Ioo 0 ρ ×ˢ Set.univ) := by
      ext w
      simp only [factor, h, true_implies, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod,
        Set.mem_Ioo, Set.mem_univ, and_true, Prod.exists]
      constructor
      · rintro ⟨hw, hw0⟩
        exact ⟨‖w‖, Complex.arg w, ⟨norm_pos_iff.mpr hw0, hw⟩, Complex.norm_mul_exp_arg_mul_I w⟩
      · rintro ⟨r, θ, ⟨hr0, hrρ⟩, rfl⟩
        have hn : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, _root_.mul_one, Complex.norm_real,
            Real.norm_of_nonneg hr0.le]
        refine ⟨by rw [hn]; exact hrρ, ?_⟩
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr0.ne') (Complex.exp_ne_zero _)
    rw [he]
    exact ((isConnected_Ioo hρ).prod isConnected_univ).image _ (by fun_prop)
  · have he : factor a ρ n i = Metric.ball 0 ρ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isConnected_ball hρ

theorem punct_open_connected_nonempty : ∀ (n a : ℕ) (ρ : ℝ), 0 < ρ → IsOpen (punct n a ρ) ∧ IsPreconnected (punct n a ρ) ∧ (punct n a ρ).Nonempty := by
  intro n a ρ hρ
  rw [punct_eq_pi n a ρ hρ]
  exact ⟨isOpen_set_pi Set.finite_univ fun i _ => isOpen_factor n a ρ i,
    isPreconnected_univ_pi fun i => (isConnected_factor n a ρ hρ i).isPreconnected,
    Set.univ_pi_nonempty_iff.mpr fun i => (isConnected_factor n a ρ hρ i).nonempty⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PunctShape
