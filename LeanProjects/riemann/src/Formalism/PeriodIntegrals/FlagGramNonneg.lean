import Mathlib

noncomputable section

open Matrix NumberField

namespace PI.FlagGramNonneg

def cT {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def HasSignature {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

def leadMinorE {E : Type} [Field E] {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) : E := by
  classical
  exact if h : l ≤ N then (A.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def gram {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) : Matrix (Fin N) (Fin N) E :=
  fun i j => hT (b i) (b j)

def IsFlag {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (T : E) (e : Fin r → V) (z : V) : Prop :=
  LinearIndependent E e ∧ (∀ a b, hT (e a) (e b) = 0) ∧ (∀ a, hT (e a) z = 0) ∧ hT z z = -T

def fvec {V : Type} {r : ℕ} (e : Fin r → V) (z : V) : Fin (r + 1) → V :=
  Fin.snoc (α := fun _ => V) e z

def zhat {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (f f' : Fin (r + 1) → V) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun a b => hT (f a) (f' b)

def gval {E : Type} [Field E] [StarRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : E :=
  leadMinorE Z (r + 1) * star (leadMinorE Z (r + 1)) - T * T' * (leadMinorE Z r * star (leadMinorE Z r))

end PI.FlagGramNonneg

namespace PI

open PI.FlagGramNonneg

def FlagGramNonneg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (hT : V →ₗ⋆[E] V →ₗ[E] E), hT.IsSymm → hT.Nondegenerate →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ),
    (∀ a, τ (star a) = starRingEnd ℂ (τ a)) →
    ∀ (p r T T' : ℕ), HasSignature ((gram hT b).map τ) p (r + 1) → 0 < T → 0 < T' →
    ∀ (e e' : Fin r → V) (z z' : V), IsFlag hT (T : E) e z → IsFlag hT (T' : E) e' z' →
      ∃ c : ℝ, 0 ≤ c ∧ τ (gval (zhat hT (fvec e z) (fvec e' z')) (T : E) (T' : E)) = c

end PI
