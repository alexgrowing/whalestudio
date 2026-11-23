import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt

namespace GlobalTheory.CovTest.SwapLine

def swapSum (d : ℕ) (a b : ℤ) : MvPolynomial (Fin 3) ℝ :=
  lin ![(a : ℝ), b, 1] ^ (d + 2) + lin ![(b : ℝ), a, 1] ^ (d + 2)

def onLine (d : ℕ) (a b : ℤ) : MvPolynomial (Fin 5) ℝ :=
  aeval ![X 0, X 3 + X 4 - X 0, X 2] (swapSum d a b)

def onBase (d : ℕ) (a b : ℤ) : MvPolynomial (Fin 5) ℝ :=
  aeval ![X 4, X 3, X 2] (swapSum d a b)

def fam5 {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
    {E : B.Modules} {h : VMetric q E 2} (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) (A : HermLB q) : Fin 5 → HermLB p :=
  ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w, (VMetric.grLB flB 0 H).pull π w,
    (VMetric.grLB flB 1 H).pull π w]

theorem swapSum_swap (d : ℕ) (a b : ℤ) : aeval ![X 1, X 0, X 2] (swapSum d a b) = swapSum d a b := by
  simp only [swapSum, map_add, map_pow, lin, Fin.sum_univ_three, map_mul, aeval_C, aeval_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    algebraMap_eq]
  ring

end GlobalTheory.CovTest.SwapLine

end
