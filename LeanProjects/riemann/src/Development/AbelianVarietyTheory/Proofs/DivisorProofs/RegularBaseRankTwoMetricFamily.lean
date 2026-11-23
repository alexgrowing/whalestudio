import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousLineBaseDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionSwapLineFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormPowersLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackHeightCompareStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.SwapLine

theorem core_exists : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ a b : ℤ, Φ (onLine d a b - onBase d a b) = Ψ (G (d + 1) a b) := by
  intro hC
  obtain ⟨G, hG, hAn⟩ := GlobalTheory.T.flag_bundle_pullback_height_compare hC
  refine ⟨G, hG, ?_⟩
  intro k _ B Y _ _ q p d hq hp hreg π w E h H flB fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨K, hKh, hK⟩ := GlobalTheory.T.homogeneous_line_base_difference d a b
  have hF : onLine d a b - onBase d a b = (X 4 - X 0) * ((X 3 - X 0) * K) := by rw [hK]; ring
  have hFv : aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) ((X 3 - X 0) * K) = 0 := by
    simp
  have hFh : ((X 3 - X 0) * K : MvPolynomial (Fin 5) ℝ).IsHomogeneous (d + 1) := by
    have h1 : (X 3 - X 0 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
      (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
    simpa [add_comm] using h1.mul hKh
  obtain ⟨r, hr, hsupp, hnorm⟩ := GlobalTheory.T.rank_two_flag_rational_sections k B Y q p d hq hp hreg π w E h H flB fl hfl A
  obtain ⟨s, c, hpol⟩ := GlobalTheory.T.homogeneous_form_powers_linear (d + 1) _ hFh
  rw [hF, GlobalTheory.T.arithmetic_function_swap_line_family hC k B Y q p d hq hp π w E h H flB fl A Φ hΦ r hr hsupp _ hFv s c hpol]
  exact hAn k B Y q p d hq hp hreg π w E h H flB fl hfl A Ψ hΨ r hr hnorm a b _ hF.symm s c hpol

end GlobalTheory.CovTest.SwapLine

end
