import Formalism.LocalToGlobal.IndefiniteReal.DatumFock

noncomputable section

open Matrix

namespace Formalism.IndefR.FockModel₂

abbrev KVar (p q n : ℕ) : Type := (Fin p ⊕ Fin q) × Fin n

variable {p q n : ℕ}

def kvSubst (k₁ : Matrix (Fin p) (Fin p) ℂ) (k₂ : Matrix (Fin q) (Fin q) ℂ) (h : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (KVar p q n) ℂ →ₐ[ℂ] MvPolynomial (KVar p q n) ℂ :=
  MvPolynomial.bind₁ fun x => match x with
    | (Sum.inl a, c) => ∑ c', ∑ a', MvPolynomial.C (h⁻¹ c c') * MvPolynomial.X (Sum.inl a', c') * MvPolynomial.C (k₁ a' a)
    | (Sum.inr b, c) => ∑ c', ∑ b', MvPolynomial.C (hᵀ c c') * MvPolynomial.X (Sum.inr b', c') *
        MvPolynomial.C (starRingEnd ℂ (k₂ b' b))

def kvLap (a : Fin p) (b : Fin q) (P : MvPolynomial (KVar p q n) ℂ) : MvPolynomial (KVar p q n) ℂ :=
  ∑ c, MvPolynomial.pderiv (Sum.inl a, c) (MvPolynomial.pderiv (Sum.inr b, c) P)

def IsKHarm (P : MvPolynomial (KVar p q n) ℂ) : Prop := ∀ a b, kvLap a b P = 0

def IsUpperUni {k : ℕ} (u : Matrix (Fin k) (Fin k) ℂ) : Prop := ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1)

def IsLowerUni {k : ℕ} (u : Matrix (Fin k) (Fin k) ℂ) : Prop := IsUpperUni uᵀ

def IsKVHW (μ₁ : Fin p → ℤ) (μ₂ : Fin q → ℤ) (ν : Fin n → ℤ) (P : MvPolynomial (KVar p q n) ℂ) : Prop :=
  (∀ u₁ u₂ u, IsUpperUni u₁ → IsUpperUni u₂ → IsLowerUni u → kvSubst u₁ u₂ u P = P) ∧
  ∀ (t₁ : Fin p → ℂ) (t₂ : Fin q → ℂ) (t : Fin n → ℂ), (∀ i, ‖t₁ i‖ = 1) → (∀ i, ‖t₂ i‖ = 1) → (∀ i, ‖t i‖ = 1) →
    kvSubst (Matrix.diagonal t₁) (Matrix.diagonal t₂) (Matrix.diagonal t) P =
      ((∏ i, t₁ i ^ μ₁ i) * (∏ i, t₂ i ^ μ₂ i) * ∏ i, t i ^ ν i) • P

def kvVar (i c : ℕ) : MvPolynomial (KVar p q n) ℂ :=
  if hc : c < n then
    (if hi : i < p then MvPolynomial.X (Sum.inl ⟨i, hi⟩, ⟨c, hc⟩)
     else if hi' : i - p < q then MvPolynomial.X (Sum.inr ⟨i - p, hi'⟩, ⟨c, hc⟩) else 0)
  else 0

def kvMinorPlus (k : ℕ) : MvPolynomial (KVar p q n) ℂ :=
  (Matrix.of fun α β : Fin k => (kvVar (p := p) (q := q) (n := n) β α)).det

def kvMinorMinus (k : ℕ) : MvPolynomial (KVar p q n) ℂ :=
  (Matrix.of fun α β : Fin k => (kvVar (p := p) (q := q) (n := n) (p + β) (n - k + α))).det

def kvDelta (ap am : ℕ → ℕ) : MvPolynomial (KVar p q n) ℂ :=
  (∏ i ∈ Finset.range p, kvMinorPlus (p := p) (q := q) (n := n) (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) *
    ∏ i ∈ Finset.range q, kvMinorMinus (p := p) (q := q) (n := n) (i + 1) ^ (am i - if i + 1 < q then am (i + 1) else 0)

def KashiwaraVergne : Prop :=
  ∀ p q n : ℕ,
    (∀ (k₁ : Matrix (Fin p) (Fin p) ℂ) (k₂ : Matrix (Fin q) (Fin q) ℂ) (h : Matrix (Fin n) (Fin n) ℂ),
      k₁ ∈ Matrix.unitaryGroup (Fin p) ℂ → k₂ ∈ Matrix.unitaryGroup (Fin q) ℂ → h ∈ Matrix.unitaryGroup (Fin n) ℂ →
      ∀ P : MvPolynomial (KVar p q n) ℂ, IsKHarm P → IsKHarm (kvSubst k₁ k₂ h P)) ∧
    (∀ μ₁ μ₂ ν (P Q : MvPolynomial (KVar p q n) ℂ), IsKHarm P → IsKHarm Q → IsKVHW μ₁ μ₂ ν P → IsKVHW μ₁ μ₂ ν Q →
      P ≠ 0 → ∃ c : ℂ, Q = c • P) ∧
    (∀ μ₁ μ₂ ν (P : MvPolynomial (KVar p q n) ℂ), IsKHarm P → IsKVHW μ₁ μ₂ ν P →
      ∃ (ap am : ℕ → ℕ) (c : ℂ), P = c • kvDelta (p := p) (q := q) (n := n) ap am)

section Fock

open Formalism.BasicNotions Formalism.IndefR.Datum

variable {D : Formalism.BasicNotions.D7} {m n : ℕ}

def lapF (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (a : Fin (p τ)) (b : Fin (m - p τ)) (P : MvPolynomial (FVar D m n) ℂ) :
    MvPolynomial (FVar D m n) ℂ :=
  ∑ c : Fin n, if h : (a : ℕ) < m ∧ p τ + (b : ℕ) < m then
    MvPolynomial.pderiv (τ, ⟨a, h.1⟩, c) (MvPolynomial.pderiv (τ, ⟨p τ + b, h.2⟩, c) P) else 0

def IsKHarmF (p : D.what₂.Tau → ℕ) (P : MvPolynomial (FVar D m n) ℂ) : Prop := ∀ τ a b, lapF p τ a b P = 0

def IsHWF (p : D.what₂.Tau → ℕ) (μ₁ : ∀ τ, Fin (p τ) → ℤ) (μ₂ : ∀ τ, Fin (m - p τ) → ℤ) (ν : D.what₂.Tau → Fin n → ℤ)
    (P : MvPolynomial (FVar D m n) ℂ) : Prop :=
  (∀ (u₁ : complexSquareMatrixFamily D p) (u₂ : complementBlockMatrixFamily D m p) (u : HFam D n),
      (∀ τ, IsUpperUni (u₁ τ)) → (∀ τ, IsUpperUni (u₂ τ)) → (∀ τ, IsLowerUni (u τ)) →
      polySubst p u₁ u₂ u P = P) ∧
  ∀ (t₁ : ∀ τ, Fin (p τ) → ℂ) (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (t : D.what₂.Tau → Fin n → ℂ),
    (∀ τ i, ‖t₁ τ i‖ = 1) → (∀ τ i, ‖t₂ τ i‖ = 1) → (∀ τ i, ‖t τ i‖ = 1) →
    polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ))
        (fun τ => Matrix.diagonal (t τ)) P =
      (∏ τ, ((∏ i, t₁ τ i ^ μ₁ τ i) * (∏ i, t₂ τ i ^ μ₂ τ i) * ∏ i, t τ i ^ ν τ i)) • P

def FockKV (D : Formalism.BasicNotions.D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) : Prop :=
  (∀ (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n),
      (∀ τ, k₁ τ ∈ Matrix.unitaryGroup (Fin (p τ)) ℂ) → (∀ τ, k₂ τ ∈ Matrix.unitaryGroup (Fin (m - p τ)) ℂ) →
      (∀ τ, h τ ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ P : MvPolynomial (FVar D m n) ℂ, IsKHarmF p P → IsKHarmF p (polySubst p k₁ k₂ h P)) ∧
  (∀ μ₁ μ₂ ν (P Q : MvPolynomial (FVar D m n) ℂ), IsKHarmF p P → IsKHarmF p Q → IsHWF p μ₁ μ₂ ν P →
      IsHWF p μ₁ μ₂ ν Q → P ≠ 0 → ∃ c : ℂ, Q = c • P) ∧
  (∀ μ₁ μ₂ ν (P : MvPolynomial (FVar D m n) ℂ), IsKHarmF p P → IsHWF p μ₁ μ₂ ν P →
      ∃ (ap am : D.what₂.Tau → ℕ → ℕ) (c : ℂ), P = c • delta p (fun τ => m - p τ) ap am)

def StepFockKV (D : Formalism.BasicNotions.D7) : Prop := KashiwaraVergne → ∀ (m n : ℕ) (p : D.what₂.Tau → ℕ), (∀ τ, p τ ≤ m) → FockKV D m n p

end Fock

end Formalism.IndefR.FockModel₂

end
