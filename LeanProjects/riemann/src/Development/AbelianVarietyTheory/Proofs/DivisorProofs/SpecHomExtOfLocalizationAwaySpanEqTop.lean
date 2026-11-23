import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem hom_ext_of_span_eq_top (S : Type) [CommRing S] (ι : Type) (s : ι → S)
    (hs : Ideal.span (Set.range s) = ⊤) (Y : Scheme.{0}) (a b : Sp S ⟶ Y)
    (h : ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a =
      spMap (algebraMap S (Localization.Away (s i))) ≫ b) :
    a = b :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
    a b h

end GlobalTheory.SecGlue
