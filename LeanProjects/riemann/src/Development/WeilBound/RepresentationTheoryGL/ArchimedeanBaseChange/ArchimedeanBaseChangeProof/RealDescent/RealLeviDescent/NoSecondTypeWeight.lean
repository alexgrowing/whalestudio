import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real
open Formalism.REAL (GlRel)

variable {n : ℕ}

def wtB (B : Finset (Fin n × Fin n)) : Fin n → ℝ := fun c =>
  ((B.filter fun p => p.1 = c).card : ℝ) - ((B.filter fun p => p.2 = c).card : ℝ)

def IsSecondTypeWeight (lam : Fin n → ℤ) (lev : Fin n → ℕ) (ν : Fin n → ℝ) : Prop :=
  ∃ B : Finset (Fin n × Fin n), B.Nonempty ∧ (∀ p ∈ B, lev p.1 < lev p.2) ∧ StrictAnti (ν + rhoV n) ∧
    ∃ w : Equiv.Perm (Fin n), ν + rhoV n = (muQ lam lev + rhoV n - wtB B) ∘ w

structure AdmFor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (lam : Fin n → ℤ) (lev : Fin n → ℕ)
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl1 : GlRel E1
  gl2 : GlRel E2
  comm : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b
  unitK : ∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ
  locFin : ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S
  ch1 : ∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x
  ch2 : ∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x
  no_second_type_weight : ∀ ν, IsSecondTypeWeight lam lev ν → hwSp E1 E2 ν = ⊥

def MultFor : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v w : V, v ∈ hwSp E1 E2 (muQ lam lev) → w ∈ hwSp E1 E2 (muQ lam lev) → v ≠ 0 →
        (∃ x ∈ alg E1 E2, x v = w) → ∃ c : ℂ, w = c • v

end PositivityTheory.RgBcC.RealD
