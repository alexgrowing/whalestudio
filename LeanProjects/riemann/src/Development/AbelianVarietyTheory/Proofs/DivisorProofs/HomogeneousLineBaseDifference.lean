import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

private theorem isHomogeneous_cast {φ : MvPolynomial (Fin 5) ℝ} {m k : ℕ} (h : φ.IsHomogeneous m) (e : m = k) :
    φ.IsHomogeneous k := e ▸ h

theorem powSum_sub_factor (t p q : MvPolynomial (Fin 5) ℝ)
    (ht : t.IsHomogeneous 1) (hp : p.IsHomogeneous 1) (hq : q.IsHomogeneous 1) (n : ℕ) :
    (∃ R : MvPolynomial (Fin 5) ℝ, R.IsHomogeneous n ∧
        t ^ (n + 2) + (p + q - t) ^ (n + 2) - p ^ (n + 2) - q ^ (n + 2) = (t - p) * (t - q) * R) ∧
      (∃ R : MvPolynomial (Fin 5) ℝ, R.IsHomogeneous (n + 1) ∧
        t ^ (n + 3) + (p + q - t) ^ (n + 3) - p ^ (n + 3) - q ^ (n + 3) = (t - p) * (t - q) * R) := by
  have hσ : (p + q).IsHomogeneous 1 := hp.add hq
  have hs : (p + q - t).IsHomogeneous 1 := hσ.sub ht
  induction n with
  | zero =>
    refine ⟨⟨1 + 1, (isHomogeneous_one (Fin 5) ℝ).add (isHomogeneous_one (Fin 5) ℝ), by ring⟩,
      ⟨(p + q) + (p + q) + (p + q), (hσ.add hσ).add hσ, by ring⟩⟩
  | succ n ih =>
    obtain ⟨⟨R₁, h₁, e₁⟩, ⟨R₂, h₂, e₂⟩⟩ := ih
    refine ⟨⟨R₂, h₂, e₂⟩, ⟨(p + q) * R₂ - t * (p + q - t) * R₁ + (p ^ (n + 2) + q ^ (n + 2)), ?_, ?_⟩⟩
    · have a₁ : ((p + q) * R₂).IsHomogeneous (n + 1 + 1) := isHomogeneous_cast (hσ.mul h₂) (by omega)
      have a₂ : (t * (p + q - t) * R₁).IsHomogeneous (n + 1 + 1) :=
        isHomogeneous_cast ((ht.mul hs).mul h₁) (by omega)
      have a₃ : (p ^ (n + 2) + q ^ (n + 2)).IsHomogeneous (n + 1 + 1) :=
        isHomogeneous_cast ((hp.pow (n + 2)).add (hq.pow (n + 2))) (by omega)
      exact (a₁.sub a₂).add a₃
    · linear_combination (p + q) * e₂ - t * (p + q - t) * e₁

theorem onLine_sub_onBase_factor (d : ℕ) (a b : ℤ) : ∃ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d ∧
    onLine d a b - onBase d a b = (X 0 - X 4) * (X 0 - X 3) * K := by
  have hX : ∀ i : Fin 5, (X i : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 := fun i => isHomogeneous_X ℝ i
  have hCX : ∀ (r : ℝ) (i : Fin 5), (C r * X i : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    fun r i => isHomogeneous_C_mul_X r i
  have ht : (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 0).add (isHomogeneous_cast ((isHomogeneous_C (Fin 5) (b : ℝ)).mul (((hX 3).add (hX 4)).sub (hX 0)))
      (by omega))).add (hX 2)
  have hp : (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 4).add (hCX _ 3)).add (hX 2)
  have hq : (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 4).add (hCX _ 3)).add (hX 2)
  obtain ⟨R, hR, e⟩ := (powSum_sub_factor _ _ _ ht hp hq d).1
  refine ⟨(C (a : ℝ) - C (b : ℝ)) ^ 2 * R, isHomogeneous_cast
    ((((isHomogeneous_C (Fin 5) (a : ℝ)).sub (isHomogeneous_C (Fin 5) (b : ℝ))).pow 2).mul hR) (by omega), ?_⟩
  have hL : onLine d a b = (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2) ^ (d + 2) +
      (C (b : ℝ) * X 0 + C (a : ℝ) * (X 3 + X 4 - X 0) + X 2) ^ (d + 2) := by
    simp only [onLine, swapSum, lin, map_add, map_pow, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_one, one_mul]
  have hB : onBase d a b = (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2) ^ (d + 2) +
      (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2) ^ (d + 2) := by
    simp only [onBase, swapSum, lin, map_add, map_pow, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_one, one_mul]
  have hs : (C (b : ℝ) * X 0 + C (a : ℝ) * (X 3 + X 4 - X 0) + X 2 : MvPolynomial (Fin 5) ℝ) =
      (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2) + (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2) -
        (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2) := by ring
  rw [hL, hB, hs]
  linear_combination e

end GlobalTheory.CovTest.SwapLine
