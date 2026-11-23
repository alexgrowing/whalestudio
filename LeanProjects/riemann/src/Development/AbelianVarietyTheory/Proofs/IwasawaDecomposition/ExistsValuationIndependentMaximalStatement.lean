import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsValuationIndependentMaximal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_independent_maximal : ∀ (K : Type) [Field K] (J : Type) [Fintype J], ∃ (Ω : Type) (_ : Field Ω) (R : ValuationSubring Ω)
    (ι : K →+* R) (s : J → R), (∀ j, s j ∈ IsLocalRing.maximalIdeal R) ∧
      (letI : Algebra K Ω := (R.subtype.comp ι).toAlgebra; AlgebraicIndependent K fun j => (s j : Ω)) := by
  first | exact @GlobalTheory.GenPert.exists_valuationSubring_algebraicIndependent_maximalIdeal | exact GlobalTheory.GenPert.exists_valuationSubring_algebraicIndependent_maximalIdeal | (intros; apply GlobalTheory.GenPert.exists_valuationSubring_algebraicIndependent_maximalIdeal <;> assumption)
