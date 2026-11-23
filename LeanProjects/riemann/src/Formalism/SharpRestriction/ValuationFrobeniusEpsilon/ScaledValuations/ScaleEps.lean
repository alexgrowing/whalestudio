import Mathlib

open MvPolynomial
noncomputable section
namespace Formalism.MainNotions.V.Lang.PsR

section generic
variable (n : ℕ) {G : Type*}

abbrev GenRing (G : Type*) := MvPolynomial (G × Fin n × Fin n) ℤ

def genMat (g : G) : Matrix (Fin n) (Fin n) (GenRing n G) := Matrix.of fun a b => X (g, a, b)

def genWord (w : FreeMonoid G) : Matrix (Fin n) (Fin n) (GenRing n G) := FreeMonoid.lift (genMat n) w
end generic

def detPoly {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {k : ℕ} (x : Fin k → Matrix ι ι R) :
    MvPolynomial (Fin k) R := (∑ j, (X j : MvPolynomial (Fin k) R) • (x j).map C).det

def Inv (n : ℕ) (G : Type*) : Subring (GenRing n G) :=
  Subring.closure {c | ∃ (k : ℕ) (w : Fin k → FreeMonoid G) (α : Fin k →₀ ℕ),
    c = coeff α (detPoly fun j => genWord n (w j))}

def invCoef (n : ℕ) {G : Type*} {k : ℕ} (w : Fin k → FreeMonoid G) (α : Fin k →₀ ℕ) : Inv n G :=
  ⟨coeff α (detPoly fun j => genWord n (w j)), Subring.subset_closure ⟨k, w, α, rfl⟩⟩

def evalW {G : Type*} [Monoid G] (w : FreeMonoid G) : G := FreeMonoid.lift id w

structure DetMon (n : ℕ) (G B : Type*) [Monoid G] [CommRing B] where
  Θ : Inv n G →+* B
  compat : ∀ (k : ℕ) (w w' : Fin k → FreeMonoid G) (α : Fin k →₀ ℕ), (∀ j, evalW (w j) = evalW (w' j)) →
    Θ (invCoef n w α) = Θ (invCoef n w' α)

structure Det (n : ℕ) (A E B : Type*) [CommRing A] [Ring E] [Algebra A E] [CommRing B] [Algebra A B] where
  D : ∀ k : ℕ, (Fin k → E) → MvPolynomial (Fin k) B
  lin : ∀ (k k' : ℕ) (y : Fin k' → E) (c : Fin k → Fin k' → A), D k (fun j => ∑ l, c j l • y l) =
    bind₁ (fun l => ∑ j, C (algebraMap A B (c j l)) * X j) (D k' y)
  Θ : Inv n E →+* B
  inv : ∀ (k : ℕ) (w : Fin k → FreeMonoid E) (α : Fin k →₀ ℕ),
    coeff α (D k fun j => evalW (w j)) = Θ (invCoef n w α)

namespace Det
variable {n : ℕ} {A E B : Type*} [CommRing A] [Ring E] [Algebra A E] [CommRing B] [Algebra A B] (D : Det n A E B)

def val (x : E) : B := eval (fun _ => 1) (D.D 1 fun _ => x)

def chi (x : E) : Polynomial B := aeval ![Polynomial.X, -1] (D.D 2 ![1, x])

def lam (i : ℕ) (x : E) : B := (aeval ![1, Polynomial.X] (D.D 2 ![1, x]) : Polynomial B).coeff i

def tr (x : E) : B := D.lam 1 x

def Kills (x : E) : Prop := ∀ (k : ℕ) (w : Fin k → E), D.D (k + 1) (Fin.cons x w) = rename Fin.succ (D.D k w)

def IsOf {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : E → Matrix ι ι B) : Prop :=
  ∀ (k : ℕ) (x : Fin k → E), D.D k x = detPoly fun j => ρ (x j)

def IsPull {A' E' B' : Type*} [CommRing A'] [Ring E'] [Algebra A' E'] [CommRing B'] [Algebra A' B']
    (D' : Det n A' E' B') (f : E' → E) (φ : B →+* B') : Prop :=
  ∀ (k : ℕ) (x : Fin k → E'), D'.D k x = map φ (D.D k (f ∘ x))
end Det

section sch
variable {n : ℕ} {A E : Type*} [CommRing A] [Ring E] [Algebra A E]

def Det.rel (D : Det n A E A) : Set E := {x | ∃ (k : ℕ) (c : Fin k → Inv n E) (w : Fin k → FreeMonoid E),
  ∑ j, (c j : GenRing n E) • genWord n (w j) = 0 ∧ x = ∑ j, D.Θ (c j) • evalW (w j)}

def Det.IsGen (D : Det n A E A) : Prop := ∀ x ∈ D.rel, x = 0
end sch

section sqz
variable {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N] [Module Aᵐᵒᵖ N] [IsCentralScalar A N]

def scaleEps (c : A) : TrivSqZeroExt A N →ₐ[A] TrivSqZeroExt A N := TrivSqZeroExt.map (c • LinearMap.id)
end sqz

def Det.IsMap {n : ℕ} {G B A : Type} [Group G] [CommRing B] [CommRing A]
    (D : Det n B (MonoidAlgebra B G) B) (D' : Det n A (MonoidAlgebra A G) A) (φ : B →+* A) : Prop :=
  ∀ (k : ℕ) (y : Fin k → MonoidAlgebra B G),
    D'.D k (fun j => MonoidAlgebra.mapRingHom G φ (y j)) = MvPolynomial.map φ (D.D k y)

end Formalism.MainNotions.V.Lang.PsR
