import Mathlib

noncomputable section

namespace GlobalTheory.SSG

def stdStep {C : Type} [CommRing C] (ϖ : C) {n : ℕ} (i : Fin n) : (Fin n → C) →ₗ[C] (Fin n → C) where
  toFun v j := if j = i then ϖ * v j else v j
  map_add' v w := by
    funext j
    by_cases h : j = i <;> simp [h, mul_add]
  map_smul' c v := by
    funext j
    by_cases h : j = i <;> simp [h, smul_eq_mul, mul_left_comm]

structure LMPoint (C : Type) [CommRing C] (ϖ : C) (n : ℕ) [NeZero n] where

  ℓ : Fin n → Submodule C (Fin n → C)

  line : ∀ i, ∃ v : Fin n → C, ℓ i = Submodule.span C {v} ∧ Ideal.span (Set.range v) = ⊤

  step : ∀ i, (ℓ i).map (stdStep ϖ i) ≤ ℓ (i + 1)

def LMPoint.worst {C : Type} [CommRing C] (n : ℕ) [NeZero n] : LMPoint C 0 n where
  ℓ i := Submodule.span C {Pi.single i 1}
  line i := ⟨Pi.single i 1, rfl, by
    rw [eq_top_iff, ← Ideal.span_singleton_one]
    exact Ideal.span_mono (by rintro _ rfl; exact ⟨i, by simp⟩)⟩
  step i := by
    rw [Submodule.map_span, Set.image_singleton]
    have : stdStep (0 : C) i (Pi.single i 1) = 0 := by
      funext j; by_cases h : j = i <;> simp [stdStep, h]
    rw [this, Submodule.span_singleton_eq_bot.2 rfl]
    exact bot_le

def chainComp {C : Type} [CommRing C] {n : ℕ} {M : Fin (n + 1) → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module C (M i)]
    (f : ∀ i : Fin n, M i.castSucc →ₗ[C] M i.succ) : ∀ i : Fin (n + 1), M 0 →ₗ[C] M i :=
  Fin.induction LinearMap.id (fun i g => f i ∘ₗ g)

end GlobalTheory.SSG

end
