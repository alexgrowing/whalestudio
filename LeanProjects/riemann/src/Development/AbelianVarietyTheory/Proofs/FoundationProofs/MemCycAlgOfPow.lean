import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne

noncomputable section

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.RecOne

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def fixA (A : ValuationSubring Ω) : Subring A where
  carrier := {a | ∀ s ∈ Ine (F := ℚ) A, s (a : Ω) = a}
  one_mem' := fun s _ => by simp
  mul_mem' := fun {a b} ha hb s hs => by
    show s ((a : Ω) * (b : Ω)) = (a : Ω) * (b : Ω)
    rw [map_mul, ha s hs, hb s hs]
  zero_mem' := fun s _ => by simp
  add_mem' := fun {a b} ha hb s hs => by
    show s ((a : Ω) + (b : Ω)) = (a : Ω) + (b : Ω)
    rw [map_add, ha s hs, hb s hs]
  neg_mem' := fun {a} ha s hs => by
    show s (-(a : Ω)) = -(a : Ω)
    rw [map_neg, ha s hs]

theorem mem_fixA {A : ValuationSubring Ω} {a : A} : a ∈ fixA A ↔ ∀ s ∈ Ine (F := ℚ) A, s (a : Ω) = a := Iff.rfl

abbrev dA (A : ValuationSubring Ω) : Derivation (fixA A) A (KaehlerDifferential (fixA A) A) :=
  KaehlerDifferential.D (fixA A) A

def cycAlg (l : ℕ) (A : ValuationSubring Ω) : Subalgebra (fixA A) A :=
  Algebra.adjoin (fixA A) {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}

theorem mem_cycAlg_of_pow {l : ℕ} {A : ValuationSubring Ω} {z : A} {n : ℕ} (h : z ^ (l ^ n) = 1) :
    z ∈ cycAlg l A := Algebra.subset_adjoin ⟨n, h⟩

def ineCyc (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) : Subgroup (G ℚ Ω) :=
  Ine (F := ℚ) A ⊓ (cycZ ℚ Ω l).ker

theorem mem_ineCyc {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {s : G ℚ Ω} :
    s ∈ ineCyc l A ↔ s ∈ Ine (F := ℚ) A ∧ cycZ ℚ Ω l s = 1 := Iff.rfl

abbrev FracA (A : ValuationSubring Ω) : Type := Ω ⧸ LinearMap.range (Algebra.linearMap A Ω)

omit [Algebra ℚ Ω] in

theorem mem_of_pow_mem (A : ValuationSubring Ω) {x : Ω} {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ∈ A) : x ∈ A := by
  rw [← A.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  by_contra hx
  push_neg at hx
  exact absurd h (not_le.2 (one_lt_pow' hx hn))

end GlobalTheory.RecOne
