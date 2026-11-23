import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionSwapLineFamily
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_function_swap_line_family : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules)
    (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)
    (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ), IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ)
      (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) →
      ∀ F : MvPolynomial (Fin 5) ℝ, aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) F = 0 →
      ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
        Φ ((X 4 - X 0) * F) = -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt
          ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr := by
  first | exact @GlobalTheory.CovTest.SwapLine.mix_dualTaut_tens_quotBase | exact GlobalTheory.CovTest.SwapLine.mix_dualTaut_tens_quotBase | (intros; apply GlobalTheory.CovTest.SwapLine.mix_dualTaut_tens_quotBase <;> assumption)
