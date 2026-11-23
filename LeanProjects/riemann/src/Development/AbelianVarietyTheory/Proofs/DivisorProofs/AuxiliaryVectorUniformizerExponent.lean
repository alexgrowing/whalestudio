import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k]

def auxiliaryVectorUniformizerExponent (a a' : ℤ) (c : ℕ) {n : Type*} : n ⊕ Fin c → ℤ
  | .inl _ => 0
  | .inr p => a * ((c : ℤ) - p) - a' * ((p : ℤ) + 1)

def vtxExp (a a' : ℤ) (c t x : ℕ) : ℤ :=
  if t ≤ x then a * ((c : ℤ) - ((x - t : ℕ) : ℤ)) - a' * (((x - t : ℕ) : ℤ) + 1) else 0

variable (G : Grid k)

def colDiag (ϖ : kˣ) (a a' : ℤ) (j : ℕ) : GL (Fin (G.rank (G.m, j))) k :=
  diagGL fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x

def boxExp (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ :=
  a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1

variable [ValuativeRel k]

def box (ϖ : kˣ) (a a' : ℤ) : Set (Vars G) :=
  Set.univ.pi fun j => Set.univ.pi fun v => {x : k | valuation k x ≤ valuation k ((ϖ ^ boxExp G a a' j v : kˣ) : k)}

variable {G}

theorem moveArgs_one_diag (g : G.VertexGroup) (d : ∀ X : ℕ × ℕ, Fin (G.rank X) → kˣ)
    (hg : ∀ X, g X = diagGL (d X)) (z : G.Args) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    G.moveArgs .one g z b r s = (d b.tgt r : k) * z b r s * ((d b.src s)⁻¹ : kˣ) := by
  have h1 : ∀ X, ((g X)⁻¹).val = diagonal fun i => (((d X i)⁻¹ : kˣ) : k) := fun X => by rw [hg]; rfl
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val]
  rw [h1, hg, diagGL_val, diagonal_transpose, diagonal_transpose, mul_diagonal, diagonal_mul]

omit [ValuativeRel k] in

theorem vtxExp_frame (a a' : ℤ) {t c b : ℕ} (h : t + c = b) (y : Fin t ⊕ Fin c) :
    vtxExp a a' c t (frame h y) = auxiliaryVectorUniformizerExponent a a' c y := by
  rcases y with x | p
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_left, x.2]
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_right]

end GlobalTheory.OriginBox
