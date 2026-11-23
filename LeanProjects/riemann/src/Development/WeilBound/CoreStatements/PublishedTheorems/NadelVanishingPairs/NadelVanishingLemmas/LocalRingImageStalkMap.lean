import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingImageStalkMap
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.local_ring_image_stalk_map : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ locRing y ↔ ∃ z ∈ stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  first | exact @_root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm | exact _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm | (intros; apply _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm <;> assumption)
