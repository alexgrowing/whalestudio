import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAicLocalSubring
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AffineProperBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jVBcS :
    VBcS := by
  intro l _ k Ω _ _ _ _ φ hl X p _ _ n i
  refine GlobalTheory.GenusTwoPureComparison.Cmp.pullHQ_bijective l _ n i fun m => ?_
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ m : ℕ) : k) := by
    push_cast
    exact hl.pow m
  exact GlobalTheory.GenusTwoPureComparison.Cmp.eqv_fieldChange UpperTheory.Et.proper_base_change UpperTheory.Et.etale_base_change_of_duality (l ^ m) k Ω φ hq p i n
