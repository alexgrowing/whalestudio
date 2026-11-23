import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt

noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure PosH (φ : V → V → ℂ) : Prop where
  add : ∀ v, ∀ w₁ w₂, φ v (w₁ + w₂) = φ v w₁ + φ v w₂
  smul : ∀ v w (r : ℂ), φ v (r • w) = r * φ v w
  herm : ∀ v w, φ w v = star (φ v w)
  pos : ∀ v, v ≠ 0 → 0 < (φ v v).re

variable {φ : V → V → ℂ}

namespace PosH

variable (h : PosH φ)
include h

theorem zero_right (v : V) : φ v 0 = 0 := by
  have := h.smul v 0 0
  simpa using this

theorem zero_left (v : V) : φ 0 v = 0 := by
  rw [h.herm v 0, h.zero_right, star_zero]

theorem add_left (v₁ v₂ w : V) : φ (v₁ + v₂) w = φ v₁ w + φ v₂ w := by
  rw [h.herm w (v₁ + v₂), h.add, star_add, ← h.herm w v₁, ← h.herm w v₂]

theorem smul_left (v w : V) (r : ℂ) : φ (r • v) w = star r * φ v w := by
  rw [h.herm w (r • v), h.smul, star_mul', ← h.herm w v]

theorem sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (b : ι → V) (w : V) :
    φ (∑ k ∈ s, c k • b k) w = ∑ k ∈ s, star (c k) * φ (b k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, h.smul_left, ih]

theorem definite (v : V) (hv : φ v v = 0) : v = 0 := by
  by_contra hne
  have := h.pos v hne
  rw [hv] at this
  simp at this

theorem re_nonneg (v : V) : 0 ≤ (φ v v).re := by
  by_cases hv : v = 0
  · subst hv; simp [h.zero_right]
  · exact (h.pos v hv).le

def perp (W : Submodule ℂ V) : Submodule ℂ V where
  carrier := {v | ∀ w ∈ W, φ w v = 0}
  add_mem' := by
    intro a b ha hb w hw
    rw [h.add, ha w hw, hb w hw, add_zero]
  zero_mem' := fun w _ => h.zero_right w
  smul_mem' := by
    intro r v hv w hw
    rw [h.smul, hv w hw, mul_zero]

theorem mem_perp (W : Submodule ℂ V) (v : V) : v ∈ h.perp W ↔ ∀ w ∈ W, φ w v = 0 := Iff.rfl

theorem inf_perp (W : Submodule ℂ V) : W ⊓ h.perp W = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rcases Submodule.mem_inf.1 hv with ⟨h1, h2⟩
  exact (Submodule.mem_bot ℂ).2 (h.definite v (h2 v h1))

end PosH

end CoreA

end PositivityTheory.Rg.Sw.LC
