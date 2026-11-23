import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

def LocFree (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E) : Prop :=
  (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) ∧
  ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ R) ∧ (∀ l, c l ∈ R) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ L) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q

def spanOver (R : Subalgebra o Ω) (S : Set E) : AddSubgroup E :=
  AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ S, v = a • e}

def GenDual (R : Subalgebra o Ω) (L : AddSubgroup E) {M : ℕ} (φ : Fin M → Module.Dual Ω E) : Prop :=
  (∀ l, ∀ v ∈ L, φ l v ∈ R) ∧
  ∀ ψ : Module.Dual Ω E, (∀ v ∈ L, ψ v ∈ R) → ∃ u : Fin M → Ω, (∀ l, u l ∈ R) ∧ ψ = ∑ l, u l • φ l

noncomputable def flagMinor {N M : ℕ} (φ : Fin M → Module.Dual Ω E) (w : Fin N → E) (i : ℕ) (hi : i ≤ N)
    (I : Fin i → Fin M) : Ω :=
  Matrix.det (Matrix.of fun a b : Fin i => φ (I a) (w (Fin.castLE hi b)))

end GlobalTheory.CompanionTheory.Ar.Num
