import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteTwistingNotIsGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVolumeParameterMaxTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEmbeddingHeightsPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationIntegralCriterionStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixedLocalChains.TermPf

theorem termSt_holds : GlobalTheory.Published.RegularAlteration → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → TermSt := by
  intro hA h2 hH D O hO p _ hp2 hU hlev
  classical
  choose jc hjc hnu using fun la : Formalism.L2.Geo.PlL D p => AdmTest.exists_placeW_nonunit D p la
  choose z _ using fun la => admEx O.S O.κ p Fact.out (placeW D p la (jc la)) (hnu la) 3 (one_add_lt_three Fact.out)
  letI := Formalism.L2.Geo.finPl D p
  refine ⟨Formalism.L2.Geo.PlL D p, Formalism.L2.Geo.finPl D p, Formalism.L2.Geo.wtL D p, fun la => placeW D p la (jc la), hnu, jc, z,
    fun la => (AdmTest.placeW_spec (hjc la)).2, ⟨Formalism.L2.Geo.wtL_sum D p, ?_, ?_⟩⟩
  · intro Sx R τ0 τ' hτ i i' hi G hG
    rw [ParamTwo.arMix_eq_max_two D O hO Sx R p]
    exact GlobalTheory.T.valuation_embedding_heights_place hA h2 hH D O hO p hp2 hU hlev _ hnu jc (fun la => (AdmTest.placeW_spec (hjc la)).2)
      (fun la => (AdmTest.placeW_spec (hjc la)).1) z Sx (max R 2) (le_max_right _ _) τ0 τ' hτ i i' hi G hG
  · intro Sx R τ0 τ' hτ i i' hi G hG
    rw [ParamTwo.arMix_eq_max_two D O hO Sx R p]
    exact GlobalTheory.T.place_valuation_integral_criterion hA h2 hH D O hO p hp2 hU hlev _ hnu jc (fun la => (AdmTest.placeW_spec (hjc la)).2)
      (fun la => (AdmTest.placeW_spec (hjc la)).1) z Sx (max R 2) (le_max_right _ _) τ0 τ' hτ i i' hi G hG

end GlobalTheory.MixedLocalChains.TermPf
