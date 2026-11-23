import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}

abbrev subStr (y : (functor A B r).obj (op T)) : y.2.1.subscheme ⟶ T :=
  y.2.1.subschemeι ≫ pullback.snd _ y.1

def Sec (y : (functor A B r).obj (op T)) (U : T.Opens) : Type :=
  Γ(y.2.1.subscheme, subStr A B y ⁻¹ᵁ U)

instance (y : (functor A B r).obj (op T)) (U : T.Opens) : CommRing (Sec A B y U) :=
  inferInstanceAs (CommRing Γ(y.2.1.subscheme, subStr A B y ⁻¹ᵁ U))

instance (y : (functor A B r).obj (op T)) (U : T.Opens) : Algebra Γ(T, U) (Sec A B y U) :=
  ((subStr A B y).app U).hom.toAlgebra

def gen (y : (functor A B r).obj (op T)) (U : T.Opens) (b : B) : Sec A B y U :=
  ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (subStr A B y ⁻¹ᵁ U) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)

def coord {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)
    (y : (functor A B r).obj (op T)) (U : T.Opens) : (Fin r → Γ(T, U)) →ₗ[Γ(T, U)] Sec A B y U :=
  Fintype.linearCombination Γ(T, U) (fun k => gen A B y U (e (σ k)))

theorem basic_iff {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)
    (y : (functor A B r).obj (op T)) :
    Basic A B e σ y ↔ ∀ U : T.affineOpens, Function.Bijective (coord A B e σ y U) := Iff.rfl

end GlobalTheory.HilbAff
