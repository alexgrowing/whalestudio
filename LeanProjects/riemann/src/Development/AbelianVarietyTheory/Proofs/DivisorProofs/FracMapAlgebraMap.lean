import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def fracMap (ρ : R →+* R') (hρ : Function.Injective ρ) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.map (A := R) (B := R') (K := FractionRing R) (L := FractionRing R') (j := ρ) hρ

theorem fracMap_algebraMap (ρ : R →+* R') (hρ : Function.Injective ρ) (r : R) :
    fracMap ρ hρ (algebraMap R _ r) = algebraMap R' _ (ρ r) := by
  simp [fracMap, IsFractionRing.map]

theorem jK_comp_spMap (ρ : R →+* R') (hρ : Function.Injective ρ) :
    jK R' ≫ spMap ρ = spMap (fracMap ρ hρ) ≫ jK R := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (fracMap_algebraMap ρ hρ r).symm

def fracAut (σ : R' ≃+* R') : FractionRing R' ≃+* FractionRing R' :=
  IsFractionRing.ringEquivOfRingEquiv σ

theorem fracAut_algebraMap (σ : R' ≃+* R') (x : R') :
    fracAut σ (algebraMap R' _ x) = algebraMap R' _ (σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x

theorem fracAut_fracMap {ρ : R →+* R'} (hρ : Function.Injective ρ) (σ : Gal ρ) (x : FractionRing R) :
    fracAut σ.1 (fracMap ρ hρ x) = fracMap ρ hρ x := by
  have h : ((fracAut σ.1).toRingHom.comp (fracMap ρ hρ)) = fracMap ρ hρ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [fracMap_algebraMap, fracAut_algebraMap, σ.2 r]
  exact congrArg (fun f : FractionRing R →+* FractionRing R' => f x) h

def genMap {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ) (β : G'.left ⟶ G.left)
    (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R) :=
  pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _ ≫ spMap (fracMap ρ hρ)) (by
    rw [Category.assoc, hβ, ← Category.assoc, pullback.condition, Category.assoc, jK_comp_spMap ρ hρ,
      Category.assoc])

theorem genMap_fst {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β :=
  pullback.lift_fst _ _ _

theorem genMap_snd {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (fracMap ρ hρ) :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.GenDesc
