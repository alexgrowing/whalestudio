import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfGenericUniqueComplexPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeepStatement
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

set_option autoImplicit false

namespace GlobalTheory.DegVal

theorem birOn_of_large_gaps : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → Hypotheses₂ → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
  intro hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  obtain ⟨f₀, hf₀, hne⟩ := GlobalTheory.T.weight_positivity_principalisation hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  obtain ⟨σ, A, B, hA, hB, hBA, hBr, hAtop, hsep⟩ := GlobalTheory.T.weight_positivity_principalisation_deep hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  have key := exists_mul_eq_of_generic_unique_complexPoint _ _ σ A B hA hB hBA hsep
  refine ⟨fun h => hne ?_, eq_top_iff.2 ?_⟩
  · have := LinearMap.congr_fun h ⟨f₀, hf₀⟩
    simpa [genPoint] using this
  · rw [← hAtop, IntermediateField.adjoin_le_iff]
    intro a ha
    obtain ⟨p, hp', q, hq', hq0, hpq⟩ := key a ha
    rw [eq_div_of_mul_eq hq0 hpq]
    exact IntermediateField.div_mem _ (hBr p hp') (hBr q hq')

end GlobalTheory.DegVal
