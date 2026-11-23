import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef

namespace GlobalTheory.HorizTrait

theorem exists_trait_of_not_mem_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (x : Z.X), x ∉ abLocus Z.t.G → ∃ (T : CDVR) (b : 𝓞 c.F →+* T.V) (io : c.F →+* T.Fr) (y : Sp T.V ⟶ Z.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp (algebraMap (𝓞 c.F) c.F) ∧ y ≫ Z.s = spMap b ∧ z ≫ pullback.snd _ _ = spMap io ∧ z ≫ Z.j = spMap (algebraMap T.V T.Fr) ≫ y ∧ y (closedPoint T.V) = x := by
  intro E _ _ _ H D l Xo c Z x _
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hβ : IsDedFrac (algebraMap (𝓞 c.F) c.F) := ⟨⟨inferInstance, inferInstance⟩, inferInstance,
    (inferInstance : IsFractionRing (𝓞 c.F) c.F)⟩
  obtain ⟨T, χ, y, hx, hy⟩ := GlobalTheory.TorRef.exists_base_trait Z hβ x
  let b : 𝓞 c.F →+* T.V := (Spec.preimage (χ ≫ Z.s)).hom
  let io : c.F →+* T.Fr := (Spec.preimage (y ≫ pullback.snd _ _)).hom
  have hb : spMap b = χ ≫ Z.s := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (χ ≫ Z.s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hio : spMap io = y ≫ pullback.snd _ _ := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (y ≫ pullback.snd _ _)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hjs : Z.j ≫ Z.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    show (Z.jQ ≫ pullback.fst _ _) ≫ Z.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over]
  refine ⟨T, b, io, χ, y, ?_, hb.symm, hio.symm, hy, hx⟩
  have key : Spec.map (CommRingCat.ofHom b ≫ CommRingCat.ofHom (algebraMap T.V T.Fr)) =
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F) ≫ CommRingCat.ofHom io) := by
    rw [Spec.map_comp, Spec.map_comp]
    change spMap (algebraMap T.V T.Fr) ≫ spMap b = spMap io ≫ spMap (algebraMap (𝓞 c.F) c.F)
    rw [hb, hio, Category.assoc]
    change jK T.V ≫ χ ≫ Z.s = _
    rw [← Category.assoc, ← hy, Category.assoc, hjs]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

end GlobalTheory.HorizTrait
