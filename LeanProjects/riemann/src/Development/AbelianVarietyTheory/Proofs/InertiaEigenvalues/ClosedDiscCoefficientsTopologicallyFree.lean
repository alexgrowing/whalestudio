import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalBasisCoeffDiscExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscTopologicalBasisExpansionStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem disc_coefficients : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap s j → ∃ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖) ∧ (∀ y, Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0)) ∧ (∀ y, HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y) ∧ (∀ y (r : ℝ), 0 ≤ r → (∀ i, ‖cD i y‖ ≤ r) → ‖y‖ ≤ r) ∧ (∀ z : ι → bk.DS ρ, Filter.Tendsto z Filter.cofinite (nhds 0) → ∃ y, ∀ i, cD i y = z i) ∧ ∀ x, ‖j x‖ = ‖x‖ := by
  intro l _ K bk A _ s ι TB ρ h0 h1 j hj
  obtain ⟨cD, hc1, hc2, hc3⟩ := GlobalTheory.T.exists_topologicalBasis_coeff_disc_extension l K bk A s ι TB ρ h0 h1 j hj
  have hs := GlobalTheory.T.closedDisc_topologicalBasis_expansion l K bk A s ι TB ρ h0 h1 j hj cD ⟨hc1, hc2, hc3⟩
  haveI : IsUltrametricDist (Disc l (s X) ρ) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).1
  have hb : ∀ (x : bk.DS ρ) (i : ι), ‖j x * toDisc l (s X) ρ (TB.b i)‖ ≤ ‖x‖ := fun x i =>
    (norm_mul_le _ _).trans ((mul_le_mul (hj.norm_le x) (norm_toDisc_le _) (norm_nonneg _)
      (norm_nonneg _)).trans (mul_one _).le)
  have hcont : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun y => (hc3 i y).trans (one_mul _).ge
  refine ⟨cD, hc1, hc2, hc3, fun y => (hs y).1, fun y => (hs y).2, ?_, ?_, ?_⟩
  · intro y r hr h
    rw [← (hs y).2.tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr fun i => (hb _ i).trans (h i)
  · intro z hz
    have ht : Filter.Tendsto (fun i => j (z i) * toDisc l (s X) ρ (TB.b i)) Filter.cofinite (nhds 0) :=
      squeeze_zero_norm (fun i => hb (z i) i) (tendsto_zero_iff_norm_tendsto_zero.1 hz)
    have hsum := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
    refine ⟨_, fun i => ((hsum.hasSum.map (cD i) (hcont i)).unique ?_)⟩
    classical
    have e : ((cD i) ∘ fun i => j (z i) * toDisc l (s X) ρ (TB.b i)) = fun i' => if i' = i then z i else 0 := by
      funext i'
      simp only [Function.comp]
      rw [hc2, hc1]
      split_ifs with h
      · subst h
        rw [TB.c_self, map_one, mul_one]
      · rw [TB.c_ne _ _ (Ne.symm h), map_zero, mul_zero]
    rw [e]
    exact hasSum_ite_eq i (z i)
  · intro x
    refine le_antisymm (hj.norm_le x) ?_
    have e : cD TB.i₀ (j x * toDisc l (s X) ρ (TB.b TB.i₀)) = x := by
      rw [hc2, hc1, TB.c_self, map_one, mul_one]
    have h := hc3 TB.i₀ (j x * toDisc l (s X) ρ (TB.b TB.i₀))
    rwa [e, TB.b_i₀, map_one, mul_one] at h

end GlobalTheory.BSP
