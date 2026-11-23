import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.FlatAcyc

theorem eq_zero_of_setIntegral_fundamentalDomain_eq_zero :
    ∀ {g : ℕ} (M : Submodule ℤ (Fl g)) (D : Set (Fl g)), IsLat M → MeasurableSet D →
      IsAddFundamentalDomain M.toAddSubgroup D volume → ∀ q : Fl g → ℝ, Continuous q →
      (∀ x, 0 ≤ q x) → (∀ l ∈ M, ∀ x, q (x + l) = q x) → IntegrableOn q D →
      ∫ x in D, q x = 0 → ∀ x, q x = 0 := by
  intro g M D hM hD hF q hq h0 hper hint hz
  obtain ⟨hdisc, _⟩ := hM
  haveI : Countable M := inferInstance
  haveI : Countable M.toAddSubgroup := this
  have h1 : q =ᵐ[volume.restrict D] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall h0) hint).1 hz
  have h2 : volume ({x | q x ≠ 0} ∩ D) = 0 := by
    rw [← Measure.restrict_apply' hD]
    exact h1
  have h3 : volume {x | q x ≠ 0} = 0 := by
    refine hF.measure_zero_of_invariant _ (fun l => ?_) h2
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have := hper _ (M.neg_mem l.2) x
    show q ((-(l : Fl g)) + x) ≠ 0 ↔ q x ≠ 0
    rw [add_comm, this]
  have h4 : q =ᵐ[volume] fun _ => 0 := h3
  have := (hq.ae_eq_iff_eq volume continuous_const).1 h4
  exact fun x => congrFun this x

end GlobalTheory.TorsionForm.FlatAcyc
