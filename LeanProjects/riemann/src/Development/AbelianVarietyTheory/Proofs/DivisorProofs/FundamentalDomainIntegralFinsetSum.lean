import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory

theorem setIntegral_finset_sum_of_periodic : ∀ {g : ℕ} (M : Submodule ℤ (Fl g)), IsLat M → ∀ (D : Set (Fl g)), IsAddFundamentalDomain M D volume → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {ι : Type} (s : Finset ι) (ψ : ι → Fl g → V), (∀ i ∈ s, Continuous (ψ i)) → (∀ i ∈ s, ∀ l ∈ M, ∀ x, ψ i (x + l) = ψ i x) → ∫ x in D, ∑ i ∈ s, ψ i x = ∑ i ∈ s, ∫ x in D, ψ i x := by
  intro g M hM D hD V _ _ _ ι s ψ hc hp
  obtain ⟨hdisc, hlat⟩ := hM
  have key : ∀ f : Fl g → V, (∀ l ∈ M, ∀ x, f (x + l) = f x) →
      ∫ x in D, f x = (ZLattice.covolume M volume) • latticeMean M f := by
    intro f hf
    rw [latticeMean_eq M volume hD hf, smul_smul,
      mul_inv_cancel₀ (ZLattice.covolume_pos M volume).ne', one_smul]
  rw [key _ (fun l hl x => Finset.sum_congr rfl fun i hi => hp i hi l hl x),
    latticeMean_finset_sum M s hc, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i hi => (key _ (hp i hi)).symm

end GlobalTheory
