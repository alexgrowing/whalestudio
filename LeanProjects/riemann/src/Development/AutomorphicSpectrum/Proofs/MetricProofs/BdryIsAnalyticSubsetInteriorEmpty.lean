import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem bdry_isAnalyticSubset_interior_empty : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsSection A L s → IsSNC A L s m W → A.IsAnalyticSubset (bdry s) ∧ interior (bdry s) = ∅ := by
  intro e X _ A L s n m W hS hSNC
  refine ⟨?_, LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC⟩
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzU⟩
    exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
  · rintro ⟨hzU, hz⟩
    exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩

end GlobalTheory.CompanionTheory.Ar.Giv
