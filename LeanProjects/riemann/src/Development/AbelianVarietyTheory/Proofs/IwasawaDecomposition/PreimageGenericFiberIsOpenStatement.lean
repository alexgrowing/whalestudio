import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageGenericFiberIsOpen
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_generic_fiber_isOpen : ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R] [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by
  first | exact @GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction | exact GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction | (intros; apply GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction <;> assumption)
