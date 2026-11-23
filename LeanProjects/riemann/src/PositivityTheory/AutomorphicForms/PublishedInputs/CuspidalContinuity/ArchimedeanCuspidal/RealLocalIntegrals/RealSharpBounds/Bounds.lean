import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.B

def eta (h : M22) : Fin 2 → ℝ := fun j => (Matrix.of h)⁻¹ 1 j

def innB (Ψ : M23 → ℂ) (h : M22) (β : ℝ) : ℂ :=
  ∫ x : Fin 2 → ℝ, Ψ (Matrix.of.symm (Matrix.of h * blk x)) * psiR (-(β * x 1))

def rt (g : GL (Fin 3) ℝ) (Ψ : M23 → ℂ) (X : M23) : ℂ :=
  Ψ (Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ)))

def pol (i j : Fin 3) (Ψ : M23 → ℂ) (X : M23) : ℂ :=
  fderiv ℝ Ψ X (Matrix.of.symm (Matrix.of X * Matrix.single i j (1 : ℝ))) + if i = j then Ψ X else 0

def secInt (k : ℕ) (Φ : Sw) (g : GL (Fin 3) ℝ) (h : M22) : ℂ :=
  Wm k (Matrix.of h)⁻¹ * inn Φ g (Matrix.of h) * sg (Matrix.of h).det *
    ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

def maj (k N : ℕ) (a b : ℝ) (h : M22) : ℝ :=
  ‖Wm k (Matrix.diagonal ![a, 1] * (Matrix.of h)⁻¹)‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) /
    ((1 + ‖h‖) ^ N * (1 + |b| * ‖eta h‖) ^ N)

def IbpBound : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ (Ψ : M23 → ℂ) (B : ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
  (∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n Ψ X‖ ≤ B) →
  ∀ (h : M22) (β : ℝ), (Matrix.of h).det ≠ 0 →
    ‖innB Ψ h β‖ ≤ C * B * |(Matrix.of h).det|⁻¹ / ((1 + ‖h‖) ^ N * (1 + |β| * ‖eta h‖) ^ N)

def MajScaled : Prop := ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ C : ℝ, ∀ (a b : ℝ), a ≠ 0 → b ≠ 0 →
  Integrable (maj k N a b) ∧ ∫ h, maj k N a b h ≤ C * |a| ^ (1 / 2 : ℝ) * |a * b| ^ (-ε)

def SecInt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (g : GL (Fin 3) ℝ), Integrable (secInt k Φ g)

def SecTo : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (ε : ℝ), 0 < ε → ∃ C : ℝ, ∀ (a b : ℝˣ), ∀ o ∈ O3,
  ‖sec k Φ (dg (a * b) b 1 * o)‖ ≤ C * |(a : ℝ)| ^ (1 - ε) * |(b : ℝ)| ^ (1 - ε)

def HasDer : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (P : Fin 3 → Fin 3 → Sw), (∀ i j X, P i j X = pol i j Φ X) →
  ∀ g : GL (Fin 3) ℝ, ∃ L : M3 →L[ℝ] ℂ, HasFDerivAt (ext (sec k Φ)) L (Matrix.of.symm (g : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    ∀ m : M3, L m = ∑ i, ∑ j, ((((g⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) * Matrix.of m) i j : ℂ) * sec k (P i j) g

end Ad3.LR.B
