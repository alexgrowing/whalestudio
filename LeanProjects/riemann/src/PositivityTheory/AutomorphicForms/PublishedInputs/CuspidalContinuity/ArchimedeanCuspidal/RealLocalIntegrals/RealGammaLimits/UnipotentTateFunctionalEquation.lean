import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped FourierTransform

namespace Ad3.LR.C

def cr (e : Bool) (s : ℂ) (r : ℝ) : ℂ := (if e ∧ r < 0 then -1 else 1) * ((|r| : ℝ) : ℂ) ^ s

def pI (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) (u : ℝ) (p : M22 × (Fin 2 → ℝ)) : ℂ :=
  Wm k (Matrix.of p.1)⁻¹ * sg (Matrix.of p.1).det * ((|(Matrix.of p.1).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
    cr (!δ) (s - 1) (p.2 1) * Φ (Matrix.of.symm (Matrix.of p.1 * blk p.2 * ((cyc u : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)))

def Pu (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) (u : ℝ) : ℂ := ∫ p, pI k Φ δ s u p

def ge (ε u : ℝ) : ℝ := Real.exp (-Real.pi * ε ^ 2 * u ^ 2)

def Hf (k : ℕ) (δ : Bool) (s : ℂ) (v : ℝ) (h : M22) : ℂ :=
  Wm k (w2 * d2 (-1 / v) * (Matrix.of h)⁻¹) * sg (-v) * cr (!δ) (-1 / 2 - s) v

def Ae (Φ : Sw) (ε : ℝ) (h : M22) (v : ℝ) : ℂ :=
  ∫ z : Fin 2 → ℝ, Φ (Matrix.of.symm (Matrix.of h * blk z)) * psiR (-(z 1)) * ge ε (z 0 - v)

def Dk (N : ℕ) (h : M22) : ℝ :=
  (max |(Matrix.of h).det| (|h 0 0 * h 0 1 + h 1 0 * h 1 1| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2)))⁻¹ / (1 + ‖h‖) ^ N

def UnipotentSubstitution : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (t : ℝˣ) (u : ℝ),
  sec k Φ (mm t u) = sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) *
    ∫ h : M22, Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      B.innB (B.rt (cyc u) Φ) h (t : ℝ)⁻¹

def UnipotentJointIntegrability : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 → ∀ u : ℝ,
  Integrable (fun p : ℝˣ × M22 => chR δ s p.1 * sg p.1 * (((|(p.1 : ℝ)|)⁻¹ : ℝ) : ℂ) *
    (Wm k (Matrix.of p.2)⁻¹ * sg (Matrix.of p.2).det * ((|(Matrix.of p.2).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      B.innB (B.rt (cyc u) Φ) p.2 (p.1 : ℝ)⁻¹)) (mulR.prod volume)

def TateFunctionalEquationComplex : Prop := ∀ (f : ℝ → ℂ) (e : Bool) (s : ℂ), 0 < s.re → s.re < 1 → Integrable f →
  Integrable (fun w => f w * ((|w| ^ (s.re - 1) : ℝ) : ℂ)) → Integrable (fun r => 𝓕 f r * ((|r| ^ (-s.re) : ℝ) : ℂ)) →
  z1 (𝓕 f) e (1 - s) = gT e s * z1 f e s

def UnipotentTateFunctionalEquation : Prop := ∀ (Ψ : M23 → ℂ) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 → ContDiff ℝ (⊤ : ℕ∞) Ψ →
  (∀ n : ℕ, ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m Ψ X‖ ≤ C) →
  ∀ h : M22, (Matrix.of h).det ≠ 0 →
    ∫ t : ℝˣ, chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) * B.innB Ψ h (t : ℝ)⁻¹ ∂mulR =
      cr (!δ) 0 (-1) * gT (!δ) s * ∫ x : Fin 2 → ℝ, cr (!δ) (s - 1) (x 1) * Ψ (Matrix.of.symm (Matrix.of h * blk x))

def PerU : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 → ∀ u : ℝ,
  Integrable (pI k Φ δ s u) ∧
    ∫ t, sec k Φ (mm t u) * chR δ s t ∂mulR = cr (!δ) 0 (-1) * gT (!δ) s * Pu k Φ δ s u

def PuBound : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 →
  ∃ (C : ℝ) (M : ℕ), ∀ u : ℝ, Integrable (pI k Φ δ s u) ∧ ∫ p, ‖pI k Φ δ s u p‖ ≤ C * (1 + |u|) ^ M

def GaussLim : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
  StInt' → Tendsto (fun ε : ℝ => ∫ u : ℝ, (ge ε u : ℂ) * ∫ t, sec k Φ (mm t u) * chR δ s t ∂mulR) (𝓝[>] 0)
    (𝓝 (∫ p : ℝˣ × ℝ, sec k Φ (mm p.1 p.2) * chR δ s p.1 ∂(mulR.prod volume)))

def CoV : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 → ∀ ε : ℝ, 0 < ε →
  ∫ u : ℝ, (ge ε u : ℂ) * Pu k Φ δ s u =
    ∫ h : M22, sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      ∫ v : ℝ, Hf k δ s v h * Ae Φ ε h v

def ParsB : Prop := ∀ (Φ : Sw) (N : ℕ), ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (h : M22) (v : ℝ),
  (Matrix.of h).det ≠ 0 → ‖Ae Φ ε h v‖ ≤ C * Dk N h

def HAbs : Prop := ∀ k : ℕ, 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ C : ℝ, ∀ (δ : Bool) (s : ℂ), s.re = σ → ∀ h : M22,
  (Matrix.of h).det ≠ 0 → Integrable (fun v => Hf k δ s v h) ∧
    ∫ v, ‖Hf k δ s v h‖ = C * |(Matrix.of h).det| ^ (σ - 1 / 2) * (h 0 1 ^ 2 + h 1 1 ^ 2) ^ ((1 - 2 * σ) / 2)

def HInt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 → ∀ h : M22, (Matrix.of h).det ≠ 0 →
  ∫ v, Hf k δ s v h = -cr δ 0 (-1) * z2' k δ s (Matrix.of h)⁻¹

def DomInt : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
  Integrable (fun h : M22 => |(Matrix.of h).det| ^ (σ - 1) * (h 0 1 ^ 2 + h 1 1 ^ 2) ^ ((1 - 2 * σ) / 2) * Dk N h)

def LimK : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 →
  Tendsto (fun ε : ℝ => ∫ h : M22, sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      ∫ v : ℝ, Hf k δ s v h * Ae Φ ε h v) (𝓝[>] 0)
    (𝓝 (∫ h : M22, inn Φ 1 (Matrix.of h) * sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      ∫ v : ℝ, Hf k δ s v h))

def Dual : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
  ∫ p : ℝˣ × ℝ, sec k Φ (mm p.1 p.2) * chR δ s p.1 ∂(mulR.prod volume) =
    gT (!δ) s * ∫ h : M22, inn Φ 1 (Matrix.of h) * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * z2' k δ s (Matrix.of h)⁻¹

end Ad3.LR.C
