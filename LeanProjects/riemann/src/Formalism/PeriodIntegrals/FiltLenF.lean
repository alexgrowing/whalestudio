import Mathlib

namespace PI

def FiltLenF : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, ↥(F k) →ₗ[R] V k),
      (∀ k, ∀ x : ↥(F k), φ k x = 0 → (x : W) ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, (M.comap (F k).subtype).map (φ k) ≤ P k) →
        (∀ k < a, Q k ≤ (N.comap (F k).subtype).map (φ k)) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)

end PI
