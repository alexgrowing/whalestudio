import Mathlib
import Formalism.LocalRingCardinality.DataTheta

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues

open Formalism.BasicNotions.TH

def lowerOp {p q : ℕ} (n : ℕ) (a : Fin p) (b : Fin q) (Φ : Pol p q n 0) : Pol p q n 0 :=
  ∑ c : Fin n, MvPolynomial.pderiv ((Sum.inl a, Sum.inl c) : Ln p q n 0)
    (MvPolynomial.pderiv ((Sum.inr b, Sum.inl c) : Ln p q n 0) Φ)

def KilledByPMinus {p q n : ℕ} (Φ : Pol p q n 0) : Prop :=
  ∀ (a : Fin p) (b : Fin q), lowerOp n a b Φ = 0

def singVal {p q : ℕ} (X : Mat p q) (i : Fin (min p q)) : ℝ :=
  (Matrix.toEuclideanLin X.toBlocks₁₂ :
    EuclideanSpace ℂ (Fin q) →ₗ[ℂ] EuclideanSpace ℂ (Fin p)).singularValues i.val

def coef {p q n : ℕ} {T₀ : GrpData (p * n + q * 0) (p * 0 + q * n)} {T₁ : GrpData p q}
    {T₂ : GrpData n 0} (F : FockData T₀ T₁ T₂) (X : Mat p q) (Φ₁ Φ₂ : Pol p q n 0) : ℂ :=
  inner ℂ (F.ι Φ₂) (F.π (T₁.expt X, 1) (F.ι Φ₁))

def HarmonicDecay : Prop :=
  ∀ (p q n : ℕ) (T₀ : GrpData (p * n + q * 0) (p * 0 + q * n)) (T₁ : GrpData p q) (T₂ : GrpData n 0)
    (F : FockData T₀ T₁ T₂) (X : Mat p q), X ∈ pR p q →
    ∀ Φ₁ Φ₂ : Pol p q n 0, KilledByPMinus Φ₁ → KilledByPMinus Φ₂ →
      ‖coef F X Φ₁ Φ₂‖ ≤
        (∏ i : Fin (min p q), Real.cosh (singVal X i) ^ (-(n : ℤ))) * ‖F.ι Φ₁‖ * ‖F.ι Φ₂‖

theorem fockAct1_lower {p q n : ℕ} (a : Fin p) (b : Fin q) (Φ : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (Sum.inr b) (Sum.inl a)) Φ = -lowerOp n a b Φ := by
  rw [fockAct1_Eab, lowerOp, LinearMap.sum_apply, Fintype.sum_sum_type, ← Finset.sum_neg_distrib]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hne : ((Sum.inr b, Sum.inl c) : Ln p q n 0) ≠ (Sum.inl a, Sum.inl c) := by simp
  have hc : ∀ (i j : Ln p q n 0) (P : Pol p q n 0),
      MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
    intro i j P
    classical
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add P Q hP hQ => simp [hP, hQ]
    | mul_X P k hP =>
      simp only [Derivation.leibniz, map_add, smul_eq_mul, hP, MvPolynomial.pderiv_X]
      by_cases h1 : k = i <;> by_cases h2 : k = j <;> simp [Pi.single_apply, h1, h2] <;>
        (try split_ifs) <;> (try simp) <;> (try ring)
  simp [omE, raiB, lowB, linePos, hne, hc (Sum.inr b, Sum.inl c) (Sum.inl a, Sum.inl c)]

example {p q n : ℕ} : KilledByPMinus (1 : Pol p q n 0) := by
  intro a b; simp [lowerOp]

example {p q n : ℕ} (a : Fin p) (c : Fin n) :
    KilledByPMinus (MvPolynomial.X (Sum.inl a, Sum.inl c) : Pol p q n 0) := by
  intro a' b
  refine Finset.sum_eq_zero fun c' _ => ?_
  rw [MvPolynomial.pderiv_X_of_ne (by simp), map_zero]

example : ¬ KilledByPMinus
    (MvPolynomial.X (Sum.inl 0, Sum.inl 0) * MvPolynomial.X (Sum.inr 0, Sum.inl 0) : Pol 1 1 1 0) := by
  intro h
  have := h 0 0
  simp [lowerOp, MvPolynomial.pderiv_X, Pi.single_apply] at this

end GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues

end
