import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapIdentityFromRegularBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousSwapRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormulaStatement

open GlobalTheory.Published GlobalTheory.CovTest

theorem GlobalTheory.CovTest.homog_swap_exists_of_ar_calc : ArCalc → RegularAlteration → ∃ G, Homog G ∧ Swap2 G := fun hC hR =>
  let ⟨G, hG, hS⟩ := GlobalTheory.T.exists_homogeneous_swap_regular hC
  ⟨G, hG, GlobalTheory.T.swap_identity_from_regular_base hC hR GlobalTheory.T.generic_degree_pullback_formula G hS⟩
