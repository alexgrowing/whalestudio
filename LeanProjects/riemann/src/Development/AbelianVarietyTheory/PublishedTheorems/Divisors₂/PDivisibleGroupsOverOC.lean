import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

noncomputable section

open CategoryTheory Ideal
open scoped TensorProduct

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup

def hodgeTateSubspace {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] (C : Type) [Field C]
    [Algebra O C] (G : PDivGroup p O) : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) :=
  LinearMap.ker (G.hodgeTateLinear.baseChange C)

def PDivisibleGroupsOverOC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x ∈ hodgeTateSubspace C G, (f.baseChange O).baseChange C x ∈ hodgeTateSubspace C H) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] (Fin h → ℤ_[p])))),
        ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
          ∀ x, x ∈ hodgeTateSubspace C G ↔ (e.toLinearMap.baseChange O).baseChange C x ∈ W

end GlobalTheory.Published
