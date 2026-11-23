import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR

abbrev M23 : Type := Fin 2 → Fin 3 → ℝ
abbrev M22 : Type := Fin 2 → Fin 2 → ℝ

abbrev Sw : Type := SchwartzMap M23 ℂ

def sg (t : ℝ) : ℂ := if t < 0 then -1 else 1

def Wm (k : ℕ) (h : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  if 0 < h.det then
    ((h.det ^ ((2 * (k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((h 1 1 : ℂ) - (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
      Complex.exp (-2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) - (h 0 0 : ℂ) * Complex.I) / ((h 1 1 : ℂ) - (h 1 0 : ℂ) * Complex.I)))
  else 0

def blk (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, x 0; 0, 1, x 1]

def inn (Φ : Sw) (g : GL (Fin 3) ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∫ x : Fin 2 → ℝ, Φ (Matrix.of.symm (h * blk x * (g : Matrix (Fin 3) (Fin 3) ℝ))) * psiR (-(x 1))

def sec (k : ℕ) (Φ : Sw) (g : GL (Fin 3) ℝ) : ℂ :=
  sg (g : Matrix (Fin 3) (Fin 3) ℝ).det * ((|(g : Matrix (Fin 3) (Fin 3) ℝ).det| : ℝ) : ℂ) *
    ∫ h : M22, Wm k (Matrix.of h)⁻¹ * inn Φ g (Matrix.of h) * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

def StLin : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ Ψ : Sw) (c : ℂ),
  sec k (Φ + Ψ) = sec k Φ + sec k Ψ ∧ sec k (c • Φ) = c • sec k Φ

def StStable : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (h : GL (Fin 3) ℝ),
  ∃ Φ' : Sw, (fun g => sec k Φ (g * h)) = sec k Φ'

def StPsi : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (x y z : ℝ) (g : GL (Fin 3) ℝ),
  sec k Φ (uni x y z * g) = psiR (x + z) * sec k Φ g

def StCen : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (a : ℝˣ) (g : GL (Fin 3) ℝ), sec k Φ (dg a a a * g) = sec k Φ g

def StSmooth : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Φ : Sw, SmoothR (sec k Φ)

def StDerCap : Prop := ∀ k : ℕ, 3 ≤ k → ∃ D : Fin 3 → Fin 3 → Module.End ℂ Sw,
  (∀ (Φ : Sw) (i j : Fin 3), der i j (sec k Φ) = sec k (D i j Φ)) ∧
  ∀ (Φ : Sw) (u : ℂ), sec k (Formalism.REAL.qdet D (u + 1) Φ) = ((u + (k - 1)) * u * (u - (k - 1))) • sec k Φ

def StQdet : Prop := ∀ (M N : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  (S : M →ₗ[ℂ] N) (D : Fin 3 → Fin 3 → Module.End ℂ M) (E : Fin 3 → Fin 3 → Module.End ℂ N),
  (∀ i j m, E i j (S m) = S (D i j m)) → ∀ (u : ℂ) (m : M), Formalism.REAL.qdet E u (S m) = S (Formalism.REAL.qdet D u m)

def StGauge : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Φ : Sw, ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ (a b : ℝˣ), ∀ o ∈ O3,
  ‖sec k Φ (dg (a * b) b 1 * o)‖ ≤ C / (|(a : ℝ)| * |(b : ℝ)|) ^ T / ((1 + |(a : ℝ)|) * (1 + |(b : ℝ)|)) ^ N

def StInt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (s : ℂ), 1 / 4 < s.re →
  Integrable (fun a => sec k Φ (dg a 1 1) * chR false (s - 1) a) mulR

def StInt' : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (s : ℂ), s.re < 3 / 4 →
  Integrable (fun p : ℝˣ × ℝ => sec k Φ (mm p.1 p.2) * chR false s p.1) (mulR.prod volume)

def StFe : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
  ∫ p : ℝˣ × ℝ, sec k Φ (mm p.1 p.2) * chR δ s p.1 ∂(mulR.prod volume) =
    gamR k δ s * ∫ a, sec k Φ (dg a 1 1) * chR δ (s - 1) a ∂mulR

def StKfin : Prop := ∀ k : ℕ, 3 ≤ k → ∃ Φ : Sw, sec k Φ ≠ 0 ∧
  FiniteDimensional ℂ (Submodule.span ℂ {W' | ∃ o ∈ O3, W' = fun g => sec k Φ (g * o)})

end Ad3.LR
