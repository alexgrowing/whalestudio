import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedSpaceOfFinGenSubfieldBaseChanges
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preconnectedSpace_of_finGen_subfield_baseChanges : ∀ (F : Type) [Field F] (X : Scheme.{0}) (f : X ⟶ Sp F), QuasiCompact f → QuasiSeparated f →
      ∀ (K : Type) [Field K] (i₀ : F →+* K),
        (∀ (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) (n : ℕ) (c : Fin n → K),
          L = Subfield.closure (Set.range i₀ ∪ Set.range c) →
          PreconnectedSpace (pullback f (spMap (i₀.codRestrict L hL)) : Scheme.{0})) →
        PreconnectedSpace (pullback f (spMap i₀) : Scheme.{0}) := by
  first | exact @GlobalTheory.GeomConnDesc.preconnectedSpace_of_finGen | exact GlobalTheory.GeomConnDesc.preconnectedSpace_of_finGen | (intros; apply GlobalTheory.GeomConnDesc.preconnectedSpace_of_finGen <;> assumption)
