import Mathlib

open Polynomial

noncomputable section

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

def nilRad {V : Type} [AddCommGroup V] [Module F V] (A : Submodule F V) : Set (Module.End F V) :=
  {h | (∀ x, h x ∈ A) ∧ ∀ x ∈ A, h x = 0}

def IsClassFn {V : Type} [AddCommGroup V] [Module F V] (φ : Module.End F V → ℂ) : Prop :=
  ∀ (e : V ≃ₗ[F] V) (g : Module.End F V), φ (e.conj g) = φ g

def IsPrimitive {V : Type} [AddCommGroup V] [Module F V] (φ : Module.End F V → ℂ) : Prop :=
  ∀ A : Submodule F V, A ≠ ⊥ → A ≠ ⊤ → ∀ g : Module.End F V, (∀ x ∈ A, g x ∈ A) →
    ∑ᶠ h ∈ nilRad A, φ (g + h) = 0

def IsAdditive (s : F[X] → ℂ) : Prop :=
  ∀ P Q : F[X], P.Monic → Q.Monic → s (P * Q) = s P + s Q

def invariantSubspaceMobiusInverseRec (s : F[X] → ℂ) (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
    Module.End F V → ℂ :=
  Nat.rec (motive := fun _ => ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
      Module.End F V → ℂ) (fun _ _ _ _ _ => 0)
    (fun _ r V _ _ _ g => s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, r W.1 (g.restrict W.2.2)) n

theorem invariantSubspaceMobiusInverseRec_succ (s : F[X] → ℂ) (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) : invariantSubspaceMobiusInverseRec s (n + 1) V g = s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, invariantSubspaceMobiusInverseRec s n W.1 (g.restrict W.2.2) := rfl

def psi (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) : ℂ :=
  invariantSubspaceMobiusInverseRec s (Module.finrank F V + 1) V g

theorem invariantSubspaceMobiusInverseRec_eq_of_finrank_lt (s : F[X] → ℂ) (n : ℕ) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V), Module.finrank F V < n → Module.finrank F V < m →
    invariantSubspaceMobiusInverseRec s n V g = invariantSubspaceMobiusInverseRec s m V g := by
  induction n with
  | zero => intro m V _ _ _ g h; omega
  | succ n ih =>
    intro m V _ _ _ g h h'
    cases m with
    | zero => omega
    | succ m =>
      rw [invariantSubspaceMobiusInverseRec_succ, invariantSubspaceMobiusInverseRec_succ]
      congr 1
      refine finsum_congr fun W => ?_
      have := Submodule.finrank_lt W.2.1
      exact ih m _ _ (by omega) (by omega)

theorem psi_eq (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) :
    psi s V g = s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) := by
  rw [psi, invariantSubspaceMobiusInverseRec_succ]
  congr 1
  refine finsum_congr fun W => ?_
  have := Submodule.finrank_lt W.2.1
  exact invariantSubspaceMobiusInverseRec_eq_of_finrank_lt s _ (Module.finrank F W.1 + 1) _ _ (by omega) (by omega)

def rootSum (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (P : F[X]) : ℂ :=
  ((P.map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).sum

def mass {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ)
    (P : F[X]) : ℂ :=
  ∑ᶠ g ∈ {g : Module.End F V | LinearMap.charpoly g = P}, φ g

def glCard (F : Type) [Field F] (n : ℕ) : ℂ := (Nat.card (GL (Fin n) F) : ℂ)

def mu (P : F[X]) : ℂ :=
  mass (fun _ : Module.End F (Fin P.natDegree → F) => (1 : ℂ)) P / glCard F P.natDegree

def mangoldt (s : F[X] → ℂ) (P : F[X]) : ℂ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ Irreducible f ∧ ∃ m : ℕ, 0 < m ∧ P = f ^ m}, s f

def conv (a b : F[X] → ℂ) (P : F[X]) : ℂ :=
  ∑ᶠ x ∈ {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}, a x.1 * b x.2

def ipGL {V : Type} [AddCommGroup V] [Module F V] (φ φ' : Module.End F V → ℂ) : ℂ :=
  ∑ᶠ g ∈ {g : Module.End F V | IsUnit g}, φ g * star (φ' g)

def extZero {d : ℕ} (χ : GL (Fin d) F → ℂ) (g : Module.End F (Fin d → F)) : ℂ :=
  ∑ᶠ x ∈ {x : GL (Fin d) F | Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g}, χ x

theorem isAdditive_natDegree : IsAdditive (fun P : F[X] => (P.natDegree : ℂ)) := by
  intro P Q hP hQ
  simp [hP.natDegree_mul hQ]

end GlobalTheory.CuspGL
