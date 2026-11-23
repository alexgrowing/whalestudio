import Formalism.CharacterColumnKernels.Statement
import Formalism.CharacterColumnKernels.StatementMF

noncomputable section

namespace Formalism.NG

universe u

section LenEpsAux

variable {O OO : Type*} [CommRing O] [Ring OO] [Algebra O OO]

lemma mem_epsImg_iff {M : Type*} [AddCommGroup M] [Module OO M] [Module O M]
    [IsScalarTower O OO M] (ε : OO) (x : M) :
    x ∈ epsImg O (M := M) ε ↔ ∃ y : M, ε • y = x := by
  simp [epsImg]

def epsMap {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A] [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) : epsImg O (M := A) ε →ₗ[O] epsImg O (M := B) ε :=
  LinearMap.restrict (φ.restrictScalars O) (fun x hx => by
    rw [mem_epsImg_iff] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨φ y, by simp⟩)

@[simp] lemma epsMap_apply {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A]
    [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) (x : epsImg O (M := A) ε) :
    ((epsMap (O := O) φ ε x : epsImg O (M := B) ε) : B) = φ x := rfl

end LenEpsAux

end Formalism.NG
