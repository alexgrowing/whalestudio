import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal Matrix

noncomputable section

abbrev Low (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}

def lowMat {r : ℕ} (w : Low r → ℂ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : b < a then w ⟨(a, b), h⟩ else if a = b then 1 else 0

def colGram {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (k : Fin (q + 1)) : ℝ := ‖lminor (Mᴴ * M) k‖

def blkW {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : Matrix (Fin (r - 1)) (Fin (r - 1)) ℂ := fun i j =>
  if p0 = 1 then lowMat w ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ else lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩

def gB {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : ℝ :=
  ∏ k : Fin (r - 1), colGram (blkW p0 w) k.castSucc ^ (-2 : ℤ)

def hB {r : ℕ} (p0 : ℕ) : (Low r → ℂ) → ℝ≥0∞ :=
  Set.indicator {w | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    fun w => ENNReal.ofReal (gB p0 w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def zOf (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Low r → ℂ := fun p =>
  z (Fintype.equivFin (Ent X) ⟨τ, p⟩)

def bnd (X : Data E r) (z : V (nd X)) : ℝ := ∏ τ, gB X.p0 (zOf X z τ)

theorem nmat_eq_lowMat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (Matrix.of (nmat X z τ) : Matrix (Fin r) (Fin r) ℂ) = lowMat (zOf X z τ) := by
  ext a b
  simp only [Matrix.of_apply, nmat, lowMat, zOf]

end

end GlobalTheory.IntBall
