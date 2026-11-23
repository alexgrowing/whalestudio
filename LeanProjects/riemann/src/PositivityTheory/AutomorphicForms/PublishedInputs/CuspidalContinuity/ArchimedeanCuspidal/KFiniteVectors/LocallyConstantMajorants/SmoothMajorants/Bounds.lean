import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.CrdcTemperate

noncomputable section

open MeasureTheory Matrix

namespace Ad3.K.LC.B

abbrev E5 : Type := M23 × (Fin 2 → ℂ)

def rt (g : GL (Fin 3) ℂ) (Ψ : E5 → ℂ) (X : E5) : ℂ :=
  Ψ (Matrix.of.symm (Matrix.of X.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), X.2)

def innB (Φ : E5 → ℂ) (h : M22) (t α β : ℂ) : ℂ :=
  ∫ p : (Fin 2 → ℂ) × ℂ, Φ (Matrix.of.symm (Matrix.of h * blk p.1), rowv t p.2 (Matrix.of h)) *
    psiC (-(β * p.1 1)) * psiC (-(α * p.2))

def eta (h : M22) : Fin 2 → ℂ := fun j => (Matrix.of h)⁻¹ 1 j

def jm (N : ℕ) (h : M22) (t α β : ℂ) : ℝ :=
  (‖(Matrix.of h).det‖ ^ 2 * ‖t‖ ^ 2 * ‖eta h‖ ^ 2)⁻¹ * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖β‖ * ‖eta h‖) ^ N)⁻¹ *
    (‖t‖ * ‖eta h‖ / (‖α‖ + ‖t‖ * ‖eta h‖)) ^ N * ((1 + ‖t‖ / (‖(Matrix.of h).det‖ * ‖eta h‖)) ^ N)⁻¹

def IbpBound : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ (Φ : E5 → ℂ) (B : ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ →
  (∀ n ≤ 2 * N, ∀ X : E5, (1 + ‖X‖) ^ (2 * N + 20) * ‖iteratedFDeriv ℝ n Φ X‖ ≤ B) →
  ∀ (h : M22) (t α β : ℂ), (Matrix.of h).det ≠ 0 → t ≠ 0 → α ≠ 0 →
    ‖innB Φ h t α β‖ ≤ C * B * jm N h t α β

def MajScaled : Prop := ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ C : ℝ, ∀ (a b : ℂ), a ≠ 0 → b ≠ 0 →
  Integrable (fun p : M22 × ℂ => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b) ∧
    ∫ p : M22 × ℂ, (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b ≤ C * (‖a‖ * ‖b‖) ^ (-ε)

def secI (k : ℕ) (Ψ : Sw) (g : GL (Fin 3) ℂ) (p : M22 × ℂ) : ℂ :=
  inn Ψ g (Matrix.of p.1) p.2 * ph (4 * (k : ℤ) - 4) p.2 * ph (-(2 * (k : ℤ) - 2)) (Matrix.of p.1).det *
    ((‖(Matrix.of p.1).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)

def SecJ : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (g : GL (Fin 3) ℂ), Integrable (secI k Ψ g)

def SecFub : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (g : GL (Fin 3) ℂ),
  sec k Ψ g = ((‖(g : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) * ∫ p : M22 × ℂ, secI k Ψ g p

def XInt : Prop := ∀ (Ψ : Sw) (g : GL (Fin 3) ℂ) (h : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ), h.det ≠ 0 → t ≠ 0 →
  Integrable (fun p : (Fin 2 → ℂ) × ℂ => Ψ (Matrix.of.symm (h * blk p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), rowv t p.2 h) *
    psiC (-(p.1 1)) * psiC (-p.2))

def SecTo : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (ε : ℝ), 0 < ε → ∃ C : ℝ, ∀ (a b : ℂˣ), ∀ o ∈ U3,
  ‖sec k Ψ (dg (a * b) b 1 * o)‖ ≤ C * ‖(a : ℂ)‖ ^ (2 - ε) * ‖(b : ℂ)‖ ^ (2 - ε)

def Sharp : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (ε : ℝ), 0 < ε → ∀ N : ℕ, ∃ C : ℝ, ∀ (a b : ℂˣ), ∀ o ∈ U3,
  ‖sec k Ψ (dg (a * b) b 1 * o)‖ * ((1 + ‖(a : ℂ)‖) * (1 + ‖(b : ℂ)‖)) ^ N ≤ C * ‖(a : ℂ)‖ ^ (2 - ε) * ‖(b : ℂ)‖ ^ (2 - ε)

def MmIw : Prop := ∀ (t : ℂˣ) (u : ℂ), ∃ (z : ℂ) (a b c : ℂˣ) (o : GL (Fin 3) ℂ), o ∈ U3 ∧
  ‖(a : ℂ)‖ = Real.sqrt (1 + ‖u‖ ^ 2) ∧ ‖(b : ℂ)‖ = 1 / (‖(t : ℂ)‖ * (1 + ‖u‖ ^ 2)) ∧
  mm t u = uni 0 0 z * dg c c c * (dg (a * b) b 1 * o)

end Ad3.K.LC.B
