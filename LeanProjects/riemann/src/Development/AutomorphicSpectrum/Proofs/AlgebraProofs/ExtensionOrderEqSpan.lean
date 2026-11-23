import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.ExtSpan

theorem extOrder_eq_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  intro R _ T _ R' _ φ A g
  set S : Set (T → R') := {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} with hS
  have hmul : ∀ {x y : T → R'}, x ∈ S → y ∈ S → x * y ∈ S := by
    rintro _ _ ⟨f1, hf1, rfl⟩ ⟨f2, hf2, rfl⟩
    exact ⟨f1 * f2, A.mul_mem hf1 hf2, by funext t; simp [map_mul]⟩
  have hone : (1 : T → R') ∈ S := ⟨1, A.one_mem, by funext t; simp⟩
  let M : Submonoid (T → R') := { carrier := S, mul_mem' := hmul, one_mem' := hone }
  have hcl : ((Submonoid.closure S : Submonoid (T → R')) : Set (T → R')) = S :=
    congrArg (fun N : Submonoid (T → R') => (N : Set (T → R'))) (Submonoid.closure_eq M)
  have hspan : Subalgebra.toSubmodule (Algebra.adjoin R' S) = Submodule.span R' S := by
    rw [Algebra.adjoin_eq_span, hcl]
  have hdef : extOrder φ A = Algebra.adjoin R' S := by
    first
    | rfl
    | (unfold extOrder; congr 1)
    | (unfold extOrder; congr 1; ext x; simp only [hS, Set.mem_setOf_eq, Set.mem_range, Set.mem_image, Subtype.exists, exists_prop, SetLike.mem_coe]; constructor <;> rintro ⟨f, hf, h⟩ <;> exact ⟨f, hf, h.symm⟩)
  rw [hdef, ← Subalgebra.mem_toSubmodule, hspan]

end GlobalTheory.CompanionTheory.Ar.BT.ExtSpan
