import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory

theorem setIntegral_fundamentalDomain_sublattice :
    ∀ {g : ℕ} (M M' : Submodule ℤ (Fl g)), IsLat M → IsLat M' → M ≤ M' → ∀ (D : Set (Fl g)), IsAddFundamentalDomain M D volume → ∃ c : ℝ, c ≠ 0 ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (ψ : Fl g → V), Continuous ψ → (∀ l ∈ M', ∀ x, ψ (x + l) = ψ x) → ∀ D' : Set (Fl g), IsAddFundamentalDomain M' D' volume → ∫ x in D, ψ x = c • ∫ x in D', ψ x := by
  intro g M M' hM hM' hle D hD
  obtain ⟨_, _⟩ := hM
  obtain ⟨_, _⟩ := hM'
  have h0 := ZLattice.covolume_pos M (volume : Measure (Fl g))
  have h0' := ZLattice.covolume_pos M' (volume : Measure (Fl g))
  refine ⟨ZLattice.covolume M volume / ZLattice.covolume M' volume, (div_pos h0 h0').ne', ?_⟩
  intro V _ _ _ ψ hψ hper D' hD'
  have hperM : ∀ l ∈ M, ∀ x, ψ (x + l) = ψ x := fun l hl x => hper l (hle hl) x
  have e1 := latticeMean_eq M volume hD hperM
  have e2 := latticeMean_eq M' volume hD' hper
  have e3 := latticeMean_eq_of_periodic M M' hψ hperM hper
  rw [e1, e2] at e3
  have := congrArg (fun v : V => ZLattice.covolume M volume • v) e3
  simp only [smul_smul, mul_inv_cancel₀ h0.ne', one_smul] at this
  rw [this, div_eq_mul_inv]

end GlobalTheory
