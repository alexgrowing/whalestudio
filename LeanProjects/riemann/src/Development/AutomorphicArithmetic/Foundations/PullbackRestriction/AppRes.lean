import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign

open CategoryTheory TopologicalSpace Opposite GlobalTheory GlobalTheory.PD

universe v u

noncomputable section

namespace UpperTheory.PullbackSkewHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type} [Ring R]

structure AltHom (τ : κ → ι) (A : Cube.{v} ι R) (B : Cube.{v} κ R) where

  app : ∀ t : Finset κ, A.obj (t.image τ) →ₗ[R] B.obj t

  app_res : ∀ {s t : Finset κ} (h : s ⊆ t) (x : A.obj (s.image τ)),
    app t (Cube.res A (Finset.image_subset_image h) x) = Cube.res B h (app s x)

namespace AltHom

variable {τ : κ → ι} {A : Cube.{v} ι R} {B : Cube.{v} κ R} (ψ : AltHom τ A B)

def term (p : ℕ) : Cube.Term A p →ₗ[R] Cube.Term B p where
  toFun x t := if h : (t.1.image τ).card = p then
    sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, h⟩) else 0
  map_add' x y := by
    funext t
    by_cases h : (t.1.image τ).card = p
    · simp only [Pi.add_apply, h, dite_true, map_add]
      exact smul_add _ _ _
    · simp [h]
  map_smul' r x := by
    funext t
    by_cases h : (t.1.image τ).card = p
    · simp only [Pi.smul_apply, h, dite_true, map_smul, RingHom.id_apply]
      exact smul_comm _ _ _
    · simp [h]

theorem term_apply (p : ℕ) (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : (t.1.image τ).card = p) :
    ψ.term p x t = sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, h⟩) := dif_pos h

theorem term_apply_of_ne (p : ℕ) (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : (t.1.image τ).card ≠ p) : ψ.term p x t = 0 := dif_neg h

end AltHom

end UpperTheory.PullbackSkewHom
