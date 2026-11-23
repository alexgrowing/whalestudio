import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth

noncomputable section

open MeasureTheory Matrix

namespace Ad3.K.LC.C

def z1 (f : ℂ → ℂ) (n : ℤ) (s : ℂ) : ℂ := ∫ a : ℂˣ, f a * chC n s a ∂mulC

def fC (f : ℂ → ℂ) (w : ℂ) : ℂ := ∫ z, f z * psiC (z * w) ∂volC

def W2 (k : ℕ) (f : (Fin 2 → ℂ) → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ph (2 * (k : ℤ) - 2) g.det * ((‖g.det‖ : ℝ) : ℂ) *
    ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t * ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] g) * psiC (-y)

def d2 (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, 0; 0, 1]

def w2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

def z2 (k : ℕ) (n : ℤ) (s : ℂ) (f : (Fin 2 → ℂ) → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∫ a : ℂˣ, W2 k f (d2 a * g) * chC n (s - 1 / 2) a ∂mulC

def z2' (k : ℕ) (n : ℤ) (s : ℂ) (f : (Fin 2 → ℂ) → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∫ a : ℂˣ, W2 k f (d2 a * w2 * g) * chC (-n) (1 / 2 - s) a ∂mulC

def g2 (k : ℕ) (n : ℤ) (s : ℂ) : ℂ := gC (n + 2 * (k - 1 : ℕ)) s * gC (n - 2 * (k - 1 : ℕ)) s

def sl (Ψ : Sw) (X : M23) : (Fin 2 → ℂ) → ℂ := fun q => Ψ (X, q)

def Wt (k : ℕ) (Ψ : Sw) (X : M23) (h : M22) : ℂ :=
  ((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * W2 k (sl Ψ X) (Matrix.of h)⁻¹

def innW (k : ℕ) (Ψ : Sw) (g : GL (Fin 3) ℂ) (h : M22) (β : ℂ) : ℂ :=
  ∫ x : Fin 2 → ℂ, Wt k Ψ (Matrix.of.symm (Matrix.of h * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ))) h * psiC (-(β * x 1))

end Ad3.K.LC.C
