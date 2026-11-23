import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.LocalFunctionalEquationFinite

noncomputable section

open MeasureTheory Matrix Complex
open scoped ComplexConjugate

namespace Ad3.K.GL2LocalData.WR

open Ad3 Ad3.LR Ad3.K.GL2LocalData

def zR (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((g 0 0 + g 1 1 : ℝ) : ℂ) + I * ((g 1 0 - g 0 1 : ℝ) : ℂ)

def nrm (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i, ∑ j, g i j ^ 2

def jj (n : ℤ) : ℕ := n.natAbs + 1

def mm (k : ℕ) (n : ℤ) : ℕ := ((2 * (k : ℤ) - 1) - (jj n : ℤ)).natAbs

def phi1 (n : ℤ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := zR g ^ jj n * ((Real.exp (-Real.pi * nrm g) : ℝ) : ℂ)

def phi2h (k : ℕ) (n : ℤ) (ξ : Fin 2 → ℝ) : ℂ :=
  ((ξ 1 : ℂ) + (if 2 * k - 1 ≤ jj n then I else -I) * (ξ 0 : ℂ)) ^ mm k n *
    ((Real.exp (-Real.pi * (ξ 0 ^ 2 + ξ 1 ^ 2)) : ℝ) : ℂ)

def c01 (X : M23) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => X i (Fin.castSucc j)
def c2 (X : M23) : Fin 2 → ℝ := fun i => X i 2

def IsPhi (k : ℕ) (n : ℤ) (Φ : Sw) (Φ₂ : (Fin 2 → ℝ) → ℂ) : Prop :=
  (∀ X, Φ X = phi1 n (c01 X) * Φ₂ (c2 X)) ∧ Integrable Φ₂ ∧
    ∀ ξ : Fin 2 → ℝ, ∫ u, Φ₂ u * Complex.exp (2 * Real.pi * I * ((ξ 0 * u 0 + ξ 1 * u 1 : ℝ) : ℂ)) = phi2h k n ξ

open Classical in

def glOf (g : Matrix (Fin 2) (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  if h : g.det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero g h else 1

def hIw (ε : Bool) (p : ℝˣ × ℝˣ × ℝ) : GL (Fin 2) ℝ := dg2 (p.1 * p.2.1) p.2.1 * kR p.2.2 ε

def realZetaIntegralGL2 (W₁ W₂ : GL (Fin 2) ℝ → ℂ) (φ : (Fin 2 → ℝ) → ℂ) (s : ℂ) : ℂ :=
  ∑ ε : Bool, ∫ p, W₁ (hIw ε p) * W₂ (hIw ε p) * φ ((hIw ε p).val 1) * chR false (s - 1) p.1 * chR false (2 * s) p.2.1 ∂mIwR

def TW (n : ℤ) (W' : GL (Fin 2) ℝ → ℂ) (s : ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  ∫ g : Fin 2 → Fin 2 → ℝ, phi1 n (Matrix.of g) * sg (Matrix.of g).det * ((|(Matrix.of g).det| : ℝ) : ℂ) ^ (s - 3 / 2) *
    W' (h * glOf (Matrix.of g))

def WmG (k : ℕ) (h : GL (Fin 2) ℝ) : ℂ := Wm k h.val

def R0 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ n : ℤ, ∃ (Φ : Sw) (Φ₂ : (Fin 2 → ℝ) → ℂ), IsPhi k n Φ Φ₂

def R1 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ n : ℤ, ∀ Φ Φ₂, IsPhi k n Φ Φ₂ → ∀ s : ℂ, 0 < s.re →
  (∀ ε, Integrable (iwR (sec k Φ) (WthR n) s ε) mIwR) ∧
    realZetaIntegralGL3GL2 (sec k Φ) (WthR n) s = realZetaIntegralGL2 (WmG k) (TW n (WthR n) s) (phi2h k n) s

def R2 : Prop := ∀ n : ℤ, ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, 0 < s.re → ∀ h,
  TW n (WthR n) s h = C * Complex.Gammaℂ (s + n.natAbs / 2) * WthR n h

def R3 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ n : ℤ, ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, 0 < s.re →
  realZetaIntegralGL2 (WmG k) (WthR n) (phi2h k n) s = C * Complex.Gammaℂ (s + (k - 1 : ℕ) + n.natAbs / 2) * Complex.Gammaℂ (s + mm k n / 2)

def RG : Prop := ∀ k : ℕ, 3 ≤ k → ∀ n : ℤ, ∀ s : ℂ,
  archimedeanGammaFactorGL3GL2 k n s = Complex.Gammaℂ (s + (k - 1 : ℕ) + n.natAbs / 2) * Complex.Gammaℂ (s + n.natAbs / 2) * Complex.Gammaℂ (s + mm k n / 2)

def RD : Prop := ∀ k : ℕ, 3 ≤ k → ∀ n : ℤ, ∀ Φ Φ₂, IsPhi k n Φ Φ₂ → ∀ C₂ C₃ : ℂ,
  (∀ s : ℂ, 0 < s.re → ∀ h, TW n (WthR n) s h = C₂ * Complex.Gammaℂ (s + n.natAbs / 2) * WthR n h) →
  (∀ s : ℂ, 0 < s.re → realZetaIntegralGL2 (WmG k) (WthR n) (phi2h k n) s =
    C₃ * Complex.Gammaℂ (s + (k - 1 : ℕ) + n.natAbs / 2) * Complex.Gammaℂ (s + mm k n / 2)) →
  ∀ s : ℂ, 0 < s.re → (∀ ε, Integrable (iwR (dW3R (sec k Φ)) (dW2R (WthR n)) s ε) mIwR) ∧
    realZetaIntegralGL3GL2 (dW3R (sec k Φ)) (dW2R (WthR n)) s = eR k n * (C₂ * C₃) * archimedeanGammaFactorGL3GL2 k n s

end Ad3.K.GL2LocalData.WR

end
