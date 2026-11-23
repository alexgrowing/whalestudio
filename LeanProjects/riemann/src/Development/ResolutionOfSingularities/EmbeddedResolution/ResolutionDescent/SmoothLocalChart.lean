import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure SmoothLocalChart {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
    {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y pY) (H : EmbeddingDatum k V pV) (u : V ⟶ Y) (y : ↥V) where
  func : Γ(H.ambient, ⊤)
  mem_domain : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  isAffine_ambient : AlgebraicGeometry.IsAffine ambient
  smooth_ambientStruct : AlgebraicGeometry.Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : AlgebraicGeometry.LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : AlgebraicGeometry.QuasiCompact ambientStruct
  toAmbient : ambient ⟶ G.ambient
  smooth_toAmbient : AlgebraicGeometry.Smooth toAmbient
  comp_eq : toAmbient ≫ G.ambientStruct = ambientStruct
  imm : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ⟶ ambient
  isClosedImmersion_imm : AlgebraicGeometry.IsClosedImmersion imm
  isPullback :
    CategoryTheory.IsPullback imm ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u) toAmbient
      G.emb

namespace SmoothLocalChart

variable {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
  {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
  {G : EmbeddingDatum k Y pY} {H : EmbeddingDatum k V pV} {u : V ⟶ Y} {y : ↥V}

abbrev chartDomain (C : SmoothLocalChart G H u y) : V.Opens :=
  H.emb ⁻¹ᵁ H.ambient.basicOpen C.func

instance instIsAffineAmbient (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.IsAffine C.ambient := C.isAffine_ambient

instance instSmoothAmbientStruct (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.Smooth C.ambientStruct := C.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.LocallyOfFiniteType C.ambientStruct :=
  C.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.QuasiCompact C.ambientStruct := C.quasiCompact_ambientStruct

instance instSmoothToAmbient (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.Smooth C.toAmbient := C.smooth_toAmbient

instance instIsClosedImmersionImm (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.IsClosedImmersion C.imm := C.isClosedImmersion_imm

theorem isAffineOpen_chartDomain [AlgebraicGeometry.IsAffine V]
    (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.IsAffineOpen C.chartDomain := by
  show AlgebraicGeometry.IsAffineOpen (H.emb ⁻¹ᵁ H.ambient.basicOpen C.func)
  have h : (H.emb ⁻¹ᵁ H.ambient.basicOpen C.func) = V.basicOpen (H.emb.app ⊤ C.func) :=
    Scheme.preimage_basicOpen H.emb C.func
  rw [h]
  exact (isAffineOpen_top V).basicOpen _

theorem isPullback_morphismRestrict_basicOpen (C : SmoothLocalChart G H u y) :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict H.emb (H.ambient.basicOpen C.func))
      C.chartDomain.ι (H.ambient.basicOpen C.func).ι H.emb :=
  AlgebraicGeometry.isPullback_morphismRestrict H.emb (H.ambient.basicOpen C.func)

end SmoothLocalChart

end FunctorialResolution.EmbeddedResolution

end
