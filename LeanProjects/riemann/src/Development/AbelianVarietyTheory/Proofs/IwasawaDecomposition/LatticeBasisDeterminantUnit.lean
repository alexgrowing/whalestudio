import Mathlib
open NumberField Matrix

namespace GlobalTheory

theorem lattice_exists_independent_family_all_embeddings
    (E : Type) [Field E] [NumberField E] (N : ℕ) (La : Type) [AddCommGroup La] [Module (𝓞 E) La]
    (Λ : Submodule (𝓞 E) (Fin N → E))
    (hspan : Submodule.span E (Λ : Set (Fin N → E)) = ⊤) (φ : La ≃ₗ[𝓞 E] Λ) :
    ∃ a : Fin N → La, ∀ (gam : La ≃ₗ[𝓞 E] La) (τ : E →+* ℂ),
      IsUnit (Matrix.of fun m l => τ ((φ (gam (a l)) : Fin N → E) m) :
        Matrix (Fin N) (Fin N) ℂ).det := by
  classical

  let B := Module.Basis.ofSpan (K := E) (V := Fin N → E) (s := (Λ : Set (Fin N → E))) hspan.ge
  let e := B.indexEquiv (Pi.basisFun E (Fin N))
  let b : Fin N → (Fin N → E) := fun l => B (e.symm l)
  have hbΛ : ∀ l, b l ∈ Λ := fun l => by
    have := Module.Basis.ofSpan_subset (K := E) (V := Fin N → E) hspan.ge
    exact this (Set.mem_range_self _)
  have hbE : LinearIndependent E b := B.linearIndependent.comp _ e.symm.injective
  have hbO : LinearIndependent (𝓞 E) b := hbE.restrict_scalars' (𝓞 E)
  let f : La →ₗ[𝓞 E] (Fin N → E) := Λ.subtype ∘ₗ φ.toLinearMap
  have hf : LinearMap.ker f = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    exact Subtype.val_injective.comp φ.injective
  let a : Fin N → La := fun l => φ.symm ⟨b l, hbΛ l⟩
  have hfa : f ∘ a = b := by
    funext l
    simp [f, a]
  have ha : LinearIndependent (𝓞 E) a := by
    apply LinearIndependent.of_comp f
    rw [hfa]; exact hbO
  refine ⟨a, fun gam τ => ?_⟩
  have h1 : LinearIndependent (𝓞 E) (gam ∘ a) := ha.map' gam.toLinearMap gam.ker
  have h2 : LinearIndependent (𝓞 E) (f ∘ (gam ∘ a)) := h1.map' f hf
  have h3 : LinearIndependent E (f ∘ (gam ∘ a)) :=
    (LinearIndependent.iff_fractionRing (𝓞 E) E).mp h2
  let M : Matrix (Fin N) (Fin N) E := Matrix.of fun m l => (φ (gam (a l)) : Fin N → E) m
  have hM : IsUnit M := by
    apply (Matrix.linearIndependent_cols_iff_isUnit).mp
    convert h3 using 1
    funext l m
    rfl
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have : (Matrix.of fun m l => τ ((φ (gam (a l)) : Fin N → E) m) :
      Matrix (Fin N) (Fin N) ℂ) = τ.mapMatrix M := by
    ext m l; simp [M]
  rw [this, ← RingHom.map_det]
  exact hdet.map τ

end GlobalTheory
