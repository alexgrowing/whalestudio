import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolDeg

theorem idlAlong_vanishingIdeal_compl (S : Scheme.{0}) (U : S.Opens) (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (f : R) (hf : (Ideal.span {f}).IsRadical) (hU : ∀ p : Sp R, ξ p ∈ (U : Set S) ↔ f ∉ p.asIdeal)
    (hrad : ∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical →
      (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) :
    idlAlong (Scheme.IdealSheafData.vanishingIdeal U.compl) ξ = Ideal.span {f} := by
  have hs := GlobalTheory.VanStalk.van_spec U.compl (ξ (closedPoint R))
  refine GlobalTheory.VanStalk.eq_of_forall_prime (hrad _ hs.1) hf fun q => ?_
  rw [idlAlong, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem]
  refine (hs.2 (PrimeSpectrum.comap (Scheme.stalkClosedPointTo ξ).hom q)).symm.trans ?_
  have e := congrArg (fun g => g q) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)
  change (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk (ξ (closedPoint R))) q ∈ (U.compl : Set S) ↔ _
  rw [e]
  change ξ q ∉ (U : Set S) ↔ _
  rw [hU q, not_not]

end GlobalTheory.PolDeg
