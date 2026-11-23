import Mathlib
import Formalism.GradedWeylDivisibility.StatementB

open MvPolynomial

noncomputable section

namespace GlobalTheory.Alc

open Formalism.GradedWeylDivisibility

def GlRel {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def shift (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) : R := μ i + ((N - 1 - i.val : ℕ) : R)

def hcMat (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i l => if l = i then shift R μ i else if i < l then -1 else 0

def hcVal (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) : R := ∑ i, ∑ l, (hcMat R μ ^ k) i l

def rowE (R : Type) [CommRing R] (r n : ℕ) : Matrix (Fin r) (Fin r) (Module.End R (MvPolynomial (Fin r × Fin n) R)) :=
  Matrix.of fun a b => ∑ s : Fin n, (LinearMap.mulLeft R (X (a, s))).comp (pderiv (b, s)).toLinearMap

def gel (R : Type) [CommRing R] (r n k : ℕ) : Module.End R (MvPolynomial (Fin r × Fin n) R) := (rowE R r n ^ k).trace

def Good {R : Type} [CommRing R] {r n : ℕ} (M : Submodule R (MvPolynomial (Fin r × Fin n) R)) : Prop :=
  (∀ a b, ∀ f ∈ M, rowE R r n a b f ∈ M) ∧
  (∀ μ : Fin r → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW r n) μ f ∈ M) ∧
  ∀ σ : Equiv.Perm (Fin r), ∀ f ∈ M, rename (fun v : Fin r × Fin n => (σ v.1, v.2)) f ∈ M

open MvPolynomial in

theorem _root_.GlobalTheory.Alc.good_top_bot (R : Type) [CommRing R] (r n : ℕ) :
    _root_.GlobalTheory.Alc.Good (⊤ : Submodule R (MvPolynomial (Fin r × Fin n) R)) ∧ _root_.GlobalTheory.Alc.Good (⊥ : Submodule R (MvPolynomial (Fin r × Fin n) R)) := by
  refine ⟨⟨fun _ _ _ _ => Submodule.mem_top, fun _ _ _ => Submodule.mem_top,
    fun _ _ _ => Submodule.mem_top⟩, ⟨?_, ?_, ?_⟩⟩
  · intro a b f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]
  · intro μ f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]
  · intro σ f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]

end GlobalTheory.Alc
