import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGaloisImagesCommuteOfComplexMultiplicaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentInertiaTateModuleFiniteResidueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageTateModuleOfBoundedExponentCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfNeronOggShafarevich
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit

theorem cmPotentialGoodReduction_of_nos (hN : GlobalTheory.Published.NeronOggShafarevichSt) :
    GlobalTheory.Published.CMPotentialGoodReductionSt := by
  intro R K _ _ _ _ _ _ _ A _ hA F _ _ hF
  have : IsCommMonObj A := hA.comm
  obtain ⟨V, hV⟩ := exists_isAbove R K (SeparableClosure K)
  obtain ⟨l, hl, hlk⟩ := GlobalTheory.Proof.exists_prime_natCast_ne_zero (ResidueField R)
  have hlK : (l : K) ≠ 0 := by
    intro h
    apply hlk
    have h1 : (l : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h])
    rw [← map_natCast (residue R), h1, map_zero]
  have hc := GlobalTheory.T.tateModule_galoisImages_commute_of_complexMultiplication K (SeparableClosure K) A hA F hF l hlK
  have he := GlobalTheory.T.exists_exponent_inertia_tateModule_finite_residue R K (SeparableClosure K) V hV A hA l hlk hc
  obtain ⟨⟨d, hd, -⟩, -⟩ := hF
  have hcard := GlobalTheory.T.card_abelianVariety_torsion_sepClosed K (SeparableClosure K) A hA d hd (l ^ 2)
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
  have hfin : Finite {x : ptOver K (SeparableClosure K) ⟶ A // x ^ (l ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (pow_ne_zero _ hl.out.ne_zero))
  exact (GlobalTheory.potentialGoodReduction_of_neronOggShafarevich hN R K (SeparableClosure K) V hV A hA l hlk).2
    (GlobalTheory.T.finite_image_tateModule_of_bounded_exponent_comm K (SeparableClosure K) A l _ hfin hc he)

end UpperTheory.Lit
