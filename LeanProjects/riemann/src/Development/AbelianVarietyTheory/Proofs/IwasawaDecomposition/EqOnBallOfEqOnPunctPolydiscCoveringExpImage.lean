import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_on_ball_of_eq_on_logExp_image : ∀ (n a : ℕ) (ρ₁ : ℝ) (X : Type) [TopologicalSpace X] [T2Space X] (f h : (Fin n → ℂ) → X), ρ₁ ≤ 1 → ContinuousOn f (Metric.ball 0 ρ₁) → ContinuousOn h (Metric.ball 0 ρ₁) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → f (logExp a s) = h (logExp a s)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, f z = h z := by
  intro n a ρ₁ X _ _ f h hρ hf hh hagree
  set U := Metric.ball (0 : Fin n → ℂ) ρ₁ with hUdef
  set D : Set (Fin n → ℂ) := {z | z ∈ U ∧ ∀ k : Fin n, (k:ℕ) < a → z k ≠ 0} with hDdef
  have hD : Set.EqOn f h D := by
    rintro z ⟨hzU, hz0⟩
    set s : Fin n → ℂ := fun k => if (k:ℕ) < a then Complex.log (z k) else z k with hsdef
    have hexp : logExp a s = z := by
      funext k
      simp only [logExp, s]
      split_ifs with hk
      · exact Complex.exp_log (hz0 k hk)
      · rfl
    have hz1 : ‖z‖ < ρ₁ := by simpa [U] using hzU
    have hnorm : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k) (lt_of_lt_of_le hz1 hρ)
    have hs : s ∈ logDom n a := by
      intro k
      simp only [s]
      split_ifs with hk
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.mpr (hz0 k hk)) (hnorm k)
      · exact hnorm k
    have := hagree s hs (by rw [hexp]; exact hzU)
    rwa [hexp] at this
  have hsub : U ⊆ closure D := by
    intro z hz
    let g : ℂ → (Fin n → ℂ) := fun t k => if (k:ℕ) < a then z k + t else z k
    have hg : Continuous g := by
      refine continuous_pi fun k => ?_
      by_cases hk : (k:ℕ) < a
      · simp only [g, hk, if_true]; fun_prop
      · simp only [g, hk, if_false]; fun_prop
    let T : Set ℂ := Set.range (fun k : Fin n => - z k)
    have hT : T.Finite := Set.finite_range _
    have hS : Dense (Set.univ \ T) := dense_univ.diff_finite hT
    have h0 : g 0 = z := by funext k; simp [g]
    have h1 : z ∈ closure (g '' (Set.univ \ T)) := by
      rw [← h0]
      exact image_closure_subset_closure_image hg
        (Set.mem_image_of_mem g (by rw [hS.closure_eq]; exact Set.mem_univ _))
    have h2 : U ∩ g '' (Set.univ \ T) ⊆ D := by
      rintro _ ⟨hU, t, ⟨-, htT⟩, rfl⟩
      refine ⟨hU, fun k hk => ?_⟩
      simp only [g, hk, if_true]
      intro heq
      exact htT ⟨k, by linear_combination -heq⟩
    exact closure_mono h2 (Metric.isOpen_ball.inter_closure ⟨hz, h1⟩)
  exact fun z hz => hD.of_subset_closure hf hh (fun x hx => hx.1) hsub hz

end GlobalTheory
