import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

namespace GlobalTheory

theorem integrableOn_periodic_of_isLat {g : ℕ} {V : Type} [NormedAddCommGroup V]
    (M : Submodule ℤ (Fl g)) (hM : IsLat M) (D : Set (Fl g))
    (hD : IsAddFundamentalDomain M D volume) (φ : Fl g → V) (hφ : Continuous φ)
    (hper : ∀ l ∈ M, ∀ x, φ (x + l) = φ x) : IntegrableOn φ D := by
  obtain ⟨hdisc, hZ⟩ := hM
  let b := Module.Free.chooseBasis ℤ M
  let bR := b.ofZLatticeBasis ℝ M
  have hspan : Submodule.span ℤ (Set.range bR) = M := b.ofZLatticeBasis_span ℝ M
  have hF : IsAddFundamentalDomain (Submodule.span ℤ (Set.range bR))
      (ZSpan.fundamentalDomain bR) volume := ZSpan.isAddFundamentalDomain bR volume
  rw [hspan] at hF
  haveI : VAddInvariantMeasure M (Fl g) volume :=
    ⟨fun c s _ => by
      show volume ((fun x => (c : Fl g) + x) ⁻¹' s) = volume s
      exact measure_preimage_add _ _ _⟩
  have hbdd : Bornology.IsBounded (ZSpan.fundamentalDomain bR) :=
    ZSpan.fundamentalDomain_isBounded bR
  have hDfin : volume D ≠ ⊤ := by
    rw [hD.measure_eq hF]; exact hbdd.measure_lt_top.ne
  have hcpt : IsCompact (φ '' closure (ZSpan.fundamentalDomain bR)) :=
    hbdd.isCompact_closure.image hφ
  obtain ⟨C, hC⟩ := hcpt.isBounded.exists_norm_le
  have hbound : ∀ x, ‖φ x‖ ≤ C := by
    intro x
    have hfl : ((ZSpan.floor bR x : Submodule.span ℤ (Set.range bR)) : Fl g) ∈ M :=
      hspan.le (ZSpan.floor bR x).2
    have hx : φ x = φ (ZSpan.fract bR x) := by
      rw [← hper _ hfl (ZSpan.fract bR x), ZSpan.fract_apply, sub_add_cancel]
    rw [hx]
    exact hC _ ⟨_, subset_closure (ZSpan.fract_mem_fundamentalDomain bR x), rfl⟩
  exact Measure.integrableOn_of_bounded hDfin hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

end GlobalTheory
