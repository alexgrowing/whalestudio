import Mathlib

noncomputable section

open Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup

section Defs

variable (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))]

abbrev Int : Subring F := (Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ))).integer

def upperBorel (r : ℕ) (k : Type) [CommRing k] : Subgroup (GL (Fin r) k) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) k).BlockTriangular id}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun {g} hg => by
    have := g.invertible
    have h := Matrix.blockTriangular_inv_of_blockTriangular hg
    simpa [Matrix.coe_units_inv] using h

def maxId : Ideal (Int F) where
  carrier := {x | Valued.v (x : F) < (1 : WithZero (Multiplicative ℤ))}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simpa using Valuation.map_add_lt _ ha hb
  smul_mem' := fun c x hx => by
    have hc : Valued.v (c : F) ≤ (1 : WithZero (Multiplicative ℤ)) := c.2
    have hx' : Valued.v (x : F) < (1 : WithZero (Multiplicative ℤ)) := hx
    show Valued.v ((c * x : Int F) : F) < (1 : WithZero (Multiplicative ℤ))
    rw [Subring.coe_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx'

def iwahoriInt (r : ℕ) : Subgroup (GL (Fin r) (Int F)) :=
  (upperBorel r (Int F ⧸ maxId F)).comap
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maxId F)))

def iwahori (r : ℕ) : Subgroup (GL (Fin r) F) :=
  (iwahoriInt F r).map (Matrix.GeneralLinearGroup.map (Int F).subtype)

variable {F}

def diagPow {r : ℕ} (ϖ : F) (a : Fin r → ℤ) : Matrix (Fin r) (Fin r) F :=
  Matrix.diagonal fun i => ϖ ^ a i

def iwahoriDoubleCoset {r : ℕ} (t : Matrix (Fin r) (Fin r) F) : Set (Matrix (Fin r) (Fin r) F) :=
  {g | ∃ i₁ ∈ iwahori F r, ∃ i₂ ∈ iwahori F r,
    g = (i₁ : Matrix (Fin r) (Fin r) F) * t * (i₂ : Matrix (Fin r) (Fin r) F)}

end Defs

def IwahoriEigenvalues : Prop :=
  ∀ (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] [CompleteSpace F]
    (ϖ : F), Valued.v ϖ = WithZero.exp (-1 : ℤ) →
    ∀ (r : ℕ) (a : Fin r → ℤ), StrictAnti a →
    ∀ g ∈ iwahoriDoubleCoset (diagPow ϖ a),
      (∃ x : Fin r → F, Function.Injective x ∧
        g.charpoly = ∏ i, (X - C (x i)) ∧
        ∀ i, Valued.v (x i) = WithZero.exp (-(a i))) ∧
      g.charpoly.Separable

theorem mem_iwahoriInt_iff (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] (r : ℕ)
    (g : GL (Fin r) (Int F)) :
    g ∈ iwahoriInt F r ↔ ∀ i j : Fin r, j < i →
      Valued.v (((g : Matrix (Fin r) (Fin r) (Int F)) i j : Int F) : F)
        < (1 : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro h i j hij
    have := h (i := i) (j := j) hij
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  · intro h i j hij
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h i j hij)

theorem self_mem_iwahoriDoubleCoset {F : Type} [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    {r : ℕ} (t : Matrix (Fin r) (Fin r) F) : t ∈ iwahoriDoubleCoset t :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

example (h : IwahoriEigenvalues) (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (r : ℕ) (a : Fin r → ℤ)
    (ha : StrictAnti a) : (diagPow ϖ a).charpoly.Separable :=
  (h _ ϖ hϖ r a ha _ (self_mem_iwahoriDoubleCoset _)).2

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup
