import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldLatticeBaseConditionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldLatticePrimeConditionStatement

set_option autoImplicit false

open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatModel

theorem modelInt : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham →
    GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement → ModelAlg → ModelInt := by
  intro hPC hST hDR hDC hPM h31 _
  intro E _ _ _ _ I _ d φ _ hd _ _ _ 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy _ lam Ω hΩ
  exact GlobalTheory.T.cm_field_lattice_prime_condition hPC hDR hDC hPM h31 E I d φ hd 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ
    (GlobalTheory.T.cm_field_lattice_base_condition hPC hST hDR hDC hPM E I d φ hd 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ)

end GlobalTheory.LatModel
