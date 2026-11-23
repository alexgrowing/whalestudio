import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesUnitaryAbsolutelyConvergentModeratStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory

theorem poincare_sum_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) → (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) → (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V, Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
  intro D θ hθ V Λ hΛ 𝔪 c
  obtain ⟨C₀, A, hC⟩ := GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth D θ hθ V Λ hΛ c
  refine ⟨C₀, A, fun u C hu hsupp hle g => ?_⟩
  have hP : ∀ x : GA D V, 0 < ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x =>
    Finset.prod_pos fun τ _ => inv_pos.2 (pow_pos (add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)) _)
  have hC0 : 0 ≤ C := by
    by_contra h
    push_neg at h
    have := hle 1
    have := hu 1
    have := mul_neg_of_neg_of_pos h (hP 1)
    linarith
  have hs : ∀ s : Finset (GQ V), ∑ γ ∈ s, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
    intro s
    classical
    set t := s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ 𝔪) with ht
    have h1 : ∑ γ ∈ s, u (c * (γ : GA D V) * g) = ∑ γ ∈ t, u (c * (γ : GA D V) * g) := by
      rw [ht, Finset.sum_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      split_ifs with h
      · rfl
      · exact hsupp _ h
    have h2 : ∑ γ ∈ t, u (c * (γ : GA D V) * g) ≤
        C * ∑ γ ∈ t, ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun γ _ => hle _
    have h3 := hC g t (fun γ hγ => congLev_mono le_top (Finset.mem_filter.1 hγ).2)
    rw [h1, mul_assoc]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hC0)
  have hsum : Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) :=
    summable_of_sum_le (fun γ => hu _) hs
  exact ⟨hsum, hsum.tsum_le_of_sum_le hs⟩

end GlobalTheory
