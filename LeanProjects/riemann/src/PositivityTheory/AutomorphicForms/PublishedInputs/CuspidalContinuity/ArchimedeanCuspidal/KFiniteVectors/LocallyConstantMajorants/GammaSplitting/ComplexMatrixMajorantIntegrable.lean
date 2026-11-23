import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.FunctionalEquationGL2GL1Complex

noncomputable section

open MeasureTheory Matrix

namespace Ad3.K.LC.C

def innQ (Ψ : Sw) (g : GL (Fin 3) ℂ) (h : M22) (β : ℂ) (q : Fin 2 → ℂ) : ℂ :=
  ∫ x : Fin 2 → ℂ, Ψ (Matrix.of.symm (Matrix.of h * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ)), q) * psiC (-(β * x 1))

def pS {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ) (f : SchwartzMap E ℂ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℝ i j f

def eta (h : M22) : Fin 2 → ℂ := fun j => (Matrix.of h)⁻¹ 1 j

def Yb (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖g.det‖ ^ 2 / (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) ^ 2

def SecQ : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (g : GL (Fin 3) ℂ),
  sec k Ψ g = ((‖(g : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) *
    ∫ h : M22, ((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ g h 1) (Matrix.of h)⁻¹

def IbpQ : Prop := ∀ N : ℕ, ∃ (C : ℝ) (N' : ℕ), ∀ (Ψ : Sw) (h : M22) (β : ℂ), (Matrix.of h).det ≠ 0 →
  ∃ f : SchwartzMap (Fin 2 → ℂ) ℂ, ⇑f = innQ Ψ 1 h β ∧
    pS N f ≤ C * pS N' Ψ * (‖(Matrix.of h).det‖ ^ 2)⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖β‖ * ‖eta h‖) ^ N)

def AbsoluteZetaIntegralBound : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ (C : ℝ) (N : ℕ),
  ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), g.det ≠ 0 →
    Integrable (fun a : ℂˣ => ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1)) mulC ∧
    ∫ a : ℂˣ, ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * σ - 1) ∂mulC ≤ C * pS N f * Yb g ^ (1 / 2 - σ)

def ComplexMatrixMajorantIntegrable : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
  Integrable (fun h : M22 => ‖(Matrix.of h).det‖ ^ (-2 - 2 * σ) * (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ (2 * σ - 1) /
    ((1 + ‖h‖) ^ N * (1 + (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) / ‖(Matrix.of h).det‖) ^ N))

def PrimPt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (a : ℂˣ),
  sec k Ψ (dg a 1 1) = ((‖(a : ℂ)‖ : ℝ) : ℂ) *
    ∫ h : M22, ((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ 1 h 1) (d2 a * (Matrix.of h)⁻¹)

def prI (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) (p : ℂˣ × M22) : ℂ :=
  ((‖(Matrix.of p.2).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ 1 p.2 1) (d2 p.1 * (Matrix.of p.2)⁻¹) * chC n (s - 1 / 2) p.1

def PrimInt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 →
  Integrable (prI k Ψ n s) (mulC.prod volume)

def Prim : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 →
  ∫ a, sec k Ψ (dg a 1 1) * chC n (s - 1) a ∂mulC =
    ∫ h : M22, ((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * z2 k n s (innQ Ψ 1 h 1) (Matrix.of h)⁻¹

end Ad3.K.LC.C
