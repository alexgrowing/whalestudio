import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace Ad3.K.LC.C

def WhittakerSchwartzBound : Prop := ∀ k : ℕ, 3 ≤ k → ∀ N : ℕ, ∃ (C : ℝ) (N' : ℕ), ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ)
  (M : Matrix (Fin 2) (Fin 2) ℂ), M.det ≠ 0 →
    ‖W2 k f M‖ ≤ C * pS N' f * Yb M ^ ((1 : ℝ) / 2) * (1 + |Real.log (Yb M)|) / (1 + Yb M) ^ N

def pI (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) (u : ℂ) (p : M22 × (Fin 2 → ℂ)) : ℂ :=
  ((‖(Matrix.of p.1).det‖⁻¹ : ℝ) : ℂ) *
    W2 k (sl Ψ (Matrix.of.symm (Matrix.of p.1 * blk p.2 * ((cyc u : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))))
      (Matrix.of p.1)⁻¹ * ph n (p.2 1) * ((‖p.2 1‖ ^ 2 : ℝ) : ℂ) ^ (s - 1)

def Pu (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) (u : ℂ) : ℂ := ∫ p, pI k Ψ n s u p

def ge (ε : ℝ) (u : ℂ) : ℝ := Real.exp (-Real.pi * ε ^ 2 * ‖u‖ ^ 2)

def Aq (Ψ : Sw) (ε : ℝ) (k : M22) (v : ℂ) (q : Fin 2 → ℂ) : ℂ :=
  ∫ z : Fin 2 → ℂ, Ψ (Matrix.of.symm (Matrix.of k * blk z), q) * psiC (-(z 1)) * (ge ε (z 0 - v) : ℂ)

def Hw (k : ℕ) (n : ℤ) (s : ℂ) (f : (Fin 2 → ℂ) → ℂ) (v : ℂ) (κ : M22) : ℂ :=
  W2 k f (w2 * d2 (-1 / v) * (Matrix.of κ)⁻¹) * ph (-n) v * ((‖v‖ ^ 2 : ℝ) : ℂ) ^ (-1 / 2 - s)

def Dk (N : ℕ) (κ : M22) : ℝ :=
  (max (‖(Matrix.of κ).det‖ ^ 2)
    (‖κ 0 0 * (starRingEnd ℂ) (κ 0 1) + κ 1 0 * (starRingEnd ℂ) (κ 1 1)‖ ^ 2 / (‖κ 0 1‖ ^ 2 + ‖κ 1 1‖ ^ 2)))⁻¹ /
    (1 + ‖κ‖) ^ N

def UnipotentSubstitution : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (t : ℂˣ) (u : ℂ),
  sec k Ψ (mm t u) = ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
    ∫ h : M22, ((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ (cyc u) h (t : ℂ)⁻¹) (Matrix.of h)⁻¹

def UnipotentJointIntegrability : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 → ∀ u : ℂ,
  Integrable (fun p : ℂˣ × M22 => chC n s p.1 * ((‖(p.1 : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
    (((‖(Matrix.of p.2).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ (cyc u) p.2 (p.1 : ℂ)⁻¹) (Matrix.of p.2)⁻¹)) (mulC.prod volume)

def UnipotentTateFunctionalEquation : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 → ∀ (g : GL (Fin 3) ℂ) (h : M22)
  (M : Matrix (Fin 2) (Fin 2) ℂ), (Matrix.of h).det ≠ 0 → M.det ≠ 0 →
    ∫ t : ℂˣ, chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * W2 k (innQ Ψ g h (t : ℂ)⁻¹) M ∂mulC =
      (1 / 2 : ℂ) * (-1) ^ n * gC n s * ∫ x : Fin 2 → ℂ, ph n (x 1) * ((‖x 1‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) *
        W2 k (sl Ψ (Matrix.of.symm (Matrix.of h * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ)))) M

def PuBound : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 →
  ∃ (C : ℝ) (M : ℕ), ∀ u : ℂ, Integrable (pI k Ψ n s u) ∧ ∫ p, ‖pI k Ψ n s u p‖ ≤ C * (1 + ‖u‖) ^ M

def PerU : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 → ∀ u : ℂ,
  ∫ t, sec k Ψ (mm t u) * chC n s t ∂mulC = (1 / 2 : ℂ) * (-1) ^ n * gC n s * Pu k Ψ n s u

def GaussLim : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
  StInt' → Tendsto (fun ε : ℝ => ∫ u : ℂ, (ge ε u : ℂ) * ∫ t, sec k Ψ (mm t u) * chC n s t ∂mulC ∂volC) (𝓝[>] 0)
    (𝓝 (∫ p : ℂˣ × ℂ, sec k Ψ (mm p.1 p.2) * chC n s p.1 ∂(mulC.prod volC)))

def CoV : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 → ∀ ε : ℝ, 0 < ε →
  ∫ u : ℂ, (ge ε u : ℂ) * Pu k Ψ n s u ∂volC =
    2 * ∫ κ : M22, ((‖(Matrix.of κ).det‖⁻¹ : ℝ) : ℂ) * ∫ v : ℂ, Hw k n s (Aq Ψ ε κ v) v κ

def ParsB : Prop := ∀ (Ψ : Sw) (N : ℕ), ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (κ : M22) (v : ℂ),
  (Matrix.of κ).det ≠ 0 → ∃ f : SchwartzMap (Fin 2 → ℂ) ℂ, ⇑f = Aq Ψ ε κ v ∧ pS N f ≤ C * Dk N κ

def HAbs : Prop := ∀ k : ℕ, 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ (C : ℝ) (N : ℕ), ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ)
  (n : ℤ) (s : ℂ), s.re = σ → ∀ κ : M22, (Matrix.of κ).det ≠ 0 → Integrable (fun v => Hw k n s f v κ) ∧
    ∫ v, ‖Hw k n s f v κ‖ ≤ C * pS N f * (‖(Matrix.of κ).det‖ ^ 2 / (‖κ 0 1‖ ^ 2 + ‖κ 1 1‖ ^ 2) ^ 2) ^ (σ - 1 / 2)

def HInt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 →
  ∀ κ : M22, (Matrix.of κ).det ≠ 0 → ∫ v, Hw k n s f v κ = (-1) ^ n * z2' k n s f (Matrix.of κ)⁻¹

def DomInt : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
  Integrable (fun κ : M22 => ‖(Matrix.of κ).det‖ ^ (2 * σ - 2) * (‖κ 0 1‖ ^ 2 + ‖κ 1 1‖ ^ 2) ^ (1 - 2 * σ) * Dk N κ)

def LimK : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 →
  Tendsto (fun ε : ℝ => ∫ κ : M22, ((‖(Matrix.of κ).det‖⁻¹ : ℝ) : ℂ) * ∫ v : ℂ, Hw k n s (Aq Ψ ε κ v) v κ) (𝓝[>] 0)
    (𝓝 (∫ κ : M22, ((‖(Matrix.of κ).det‖⁻¹ : ℝ) : ℂ) * ∫ v : ℂ, Hw k n s (innQ Ψ 1 κ 1) v κ))

def Dual : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
  ∫ p : ℂˣ × ℂ, sec k Ψ (mm p.1 p.2) * chC n s p.1 ∂(mulC.prod volC) =
    gC n s * ∫ κ : M22, ((‖(Matrix.of κ).det‖⁻¹ : ℝ) : ℂ) * z2' k n s (innQ Ψ 1 κ 1) (Matrix.of κ)⁻¹

end Ad3.K.LC.C
