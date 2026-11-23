import Mathlib

noncomputable section

namespace MassDataIdxFrA

variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]

def IntVec (v : ι → F) : Prop := ∀ i, v i ∈ O

def CongSpan (S : Set (ι → F)) (v : ι → F) : Prop :=
  ∃ w ∈ Submodule.span O S, ∃ z : ι → F, IntVec O z ∧ v = w + (γ : F) • z

omit [DecidableEq ι] in
theorem intVec_add {v w : ι → F} (hv : IntVec O v) (hw : IntVec O w) : IntVec O (v + w) := by
  exact fun i => add_mem (hv i) (hw i)

omit [DecidableEq ι] in
theorem intVec_smul (c : O) {v : ι → F} (hv : IntVec O v) : IntVec O ((c : F) • v) := by
  exact fun i => mul_mem c.2 (hv i)

section Mat

open Matrix

variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem intVec_mulVec (M : Matrix ι ι F) (hM : ∀ i j, M i j ∈ O) {z : ι → F} (hz : IntVec O z) :
    IntVec O (M *ᵥ z) := by
  intro i
  show (∑ j, M i j * z j) ∈ O
  exact sum_mem fun j _ => mul_mem (hM i j) (hz j)

theorem congSpan_zero (S : Set (ι → F)) : CongSpan O γ S 0 := by
  exact ⟨0, zero_mem _, 0, fun _ => zero_mem _, by simp⟩

theorem congSpan_neg (S : Set (ι → F)) (v : ι → F) : CongSpan O γ S (-v) ↔ CongSpan O γ S v := by
  have key : ∀ x, CongSpan O γ S x → CongSpan O γ S (-x) := by
    rintro x ⟨w, hw, z, hz, rfl⟩
    exact ⟨-w, neg_mem hw, -z, fun i => neg_mem (hz i), by rw [smul_neg, neg_add]⟩
  exact ⟨fun h => by simpa using key _ h, key v⟩

end Mat

end MassDataIdxFrA
