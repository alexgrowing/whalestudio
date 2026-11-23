import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne

open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_adjoin_mem_span : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] (s : Set S) (D : S → M), IsDerOn (Algebra.adjoin A s) D →
    ∀ x ∈ Algebra.adjoin A s, D x ∈ Submodule.span S (D '' s) := by
  intro A S M _ _ _ _ _ s D hD x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | algebraMap r => rw [hD.alg]; exact zero_mem _
  | add x y hx hy ihx ihy => rw [hD.add x hx y hy]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [hD.mul x hx y hy]
    exact add_mem (Submodule.smul_mem _ _ ihy) (Submodule.smul_mem _ _ ihx)

end GlobalTheory.AlmostEt
