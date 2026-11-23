import Formalism.IncomingBounds.IncomingBound

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

abbrev PVar (n0 : ℕ) := (Fin n0 × Fin n0) ⊕ (Fin n0 × Fin n0)

variable {C : Type} [Field C]

def detL (C : Type) [Field C] (n0 : ℕ) : MvPolynomial (PVar n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inl (b, c)))

def detR (C : Type) [Field C] (n0 : ℕ) : MvPolynomial (PVar n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inr (b, c)))

def mfact {σ : Type} (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial

def jetAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ m ∈ P.support, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m g

def mvExp {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun m => ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C)

def expE (l i : ℕ) : ℕ := 1 + l * ∑ t ∈ Finset.range ((i - 1) / 2), (l ^ 2) ^ t

def hP (C : Type) [Field C] (l i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) C) :
    MvPowerSeries (PVar n0) C :=
  -((l : C) ^ (expE l i))⁻¹ • (∑ b : Fin n0, ∑ c : Fin n0,
      MvPowerSeries.X (Sum.inl (b, c)) ^ (l ^ i) * MvPowerSeries.X (Sum.inr (b, c))) + h1

def LamP (C : Type) [Field C] (l i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) C) (y : ℕ) : C :=
  jetAt0 (detL C n0 ^ (l ^ i * y) * detR C n0 ^ y) (mvExp (hP C l i n0 h1))

def degL {n0 : ℕ} (m : PVar n0 →₀ ℕ) : ℕ := ∑ b : Fin n0, ∑ c : Fin n0, m (Sum.inl (b, c))

def degR {n0 : ℕ} (m : PVar n0 →₀ ℕ) : ℕ := ∑ b : Fin n0, ∑ c : Fin n0, m (Sum.inr (b, c))

def WeightCond (v : AddValuation C (WithTop ℝ)) (l i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) C) :
    Prop :=
  ∀ m : PVar n0 →₀ ℕ,
    (((1 / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) ≤
      v (MvPowerSeries.coeff m h1) +
        (((degL m : ℝ) * (rho l + ((l : ℝ) ^ i)⁻¹ / 2 - ((l : ℝ) ^ i)⁻¹ / 8) +
          (degR m : ℝ) * (rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8) : ℝ) : WithTop ℝ)

def diffOp {σ : Type} (P Q : MvPolynomial σ C) : MvPolynomial σ C :=
  ∑ m ∈ P.support, ∑ a ∈ Q.support,
    if m ≤ a then
      MvPolynomial.monomial (a - m)
        (MvPolynomial.coeff m P * MvPolynomial.coeff a Q * ((mfact a : C) / (mfact (a - m) : C)))
    else 0

def CayleyId : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 s : ℕ),
    diffOp (detL C n0) (detL C n0 ^ (s + 1)) =
      ((∏ a ∈ Finset.range n0, ((s : C) + 1 + a))) • detL C n0 ^ s

def ThmP : Prop :=
  ∃ C0 : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (i : ℕ), Odd i → ∀ (n n0 : ℕ), 1 ≤ n → n0 ≤ n →
    ∀ h1 : MvPowerSeries (PVar n0) C, MvPowerSeries.constantCoeff h1 = 0 →
      WeightCond v l i n0 h1 →
      ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧
        (y : ℝ) < Y0 + C0 * (n : ℝ) ^ 2 * (l : ℝ) ^ i * Real.log ((n : ℝ) * (l : ℝ) ^ i) ∧
        v (LamP C l i n0 h1 y) ≤
          ((((n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1)) : ℝ) :
            WithTop ℝ)

def ThmPFromCayley : Prop := CayleyId → ThmP

end Formalism.IncomingBounds
