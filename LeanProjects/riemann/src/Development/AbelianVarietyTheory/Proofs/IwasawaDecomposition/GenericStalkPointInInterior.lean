import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem fromSpecStalk_bot_mem_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X) (p : PrimeSpectrum (Z.X.presheaf.stalk z)),
    p.asIdeal = ⊥ → Z.X.fromSpecStalk z p ∈ Set.range Z.j := by
  intro E _ _ _ H D l Xo c Z z p hp
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI hdom : IsDomain (Z.X.presheaf.stalk z) := (Z.normal z).1
  have hfl : (Scheme.stalkClosedPointTo (Z.X.fromSpecStalk z)).hom.Flat := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    exact RingHom.Flat.of_bijective (Iso.commRingCatIsoToRingEquiv _).bijective
  obtain ⟨y, hy⟩ := @DomFine.exists_generic_point (𝓞 c.F) c.F _ _ _ _ _ Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense (Z.X.presheaf.stalk z) _ hdom _ (Z.X.fromSpecStalk z) hfl
  let w : PrimeSpectrum (FractionRing (Z.X.presheaf.stalk z)) := ⊥
  have hw : (jK (Z.X.presheaf.stalk z)) w = p := by
    apply PrimeSpectrum.ext
    rw [hp]
    show Ideal.comap (algebraMap (Z.X.presheaf.stalk z) (FractionRing (Z.X.presheaf.stalk z))) (⊥ : Ideal _) = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _)
  refine ⟨y w, ?_⟩
  have e := congrArg (fun f => f w) hy
  simp only [Scheme.Hom.comp_apply] at e
  rw [← hw]
  exact e

end GlobalTheory.TorRef
