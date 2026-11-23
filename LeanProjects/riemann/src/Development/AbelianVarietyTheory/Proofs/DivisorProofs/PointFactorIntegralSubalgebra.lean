import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.point_factor_integral_subalgebra : ∀ (K B E : Type) [Field K] [CommRing B] [CommRing E]
    [Algebra K B] [Algebra K E] (i : E →ₐ[K] B), Function.Injective i →
    (∀ b : B, _root_.IsIntegral K b → b ∈ i.range) → ∀ (T : Scheme.{0}) (p : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)
    [IsFinite p] (t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp B ⟶ T), t ≫ p = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K B) →
    ∃ u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp E ⟶ T, u ≫ p = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K E) ∧ t = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i.toRingHom ≫ u := by
  intro K B E _ _ _ _ _ i hi hint T p _ t ht
  have : IsAffine T := isAffine_of_isAffineHom p
  set e := T.isoSpec
  let φ := Spec.preimage (e.inv ≫ p)
  let α := Spec.preimage (t ≫ e.hom)
  have hφ : Spec.map φ = e.inv ≫ p := Spec.map_preimage _
  have hα : Spec.map α = t ≫ e.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  have hcomp : φ ≫ α = CommRingCat.ofHom (algebraMap K B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hφ]
    simpa [Category.assoc] using ht
  have hαφ : α.hom.comp φ.hom = algebraMap K B := by
    rw [← CommRingCat.hom_comp, hcomp, CommRingCat.hom_ofHom]
  have hmem : ∀ a, α.hom a ∈ i.range := by
    intro a
    apply hint
    obtain ⟨P, hP, hPa⟩ := hfin.to_isIntegral a
    refine ⟨P, hP, ?_⟩
    have h2 := congrArg α.hom hPa
    rw [Polynomial.hom_eval₂, map_zero, hαφ] at h2
    exact h2
  let eqv := AlgEquiv.ofInjective i hi
  let β : Γ(T, ⊤) →+* E := eqv.symm.toRingHom.comp (α.hom.codRestrict i.range hmem)
  have hiβ : ∀ a, i (β a) = α.hom a := by
    intro a
    change i (eqv.symm ⟨α.hom a, hmem a⟩) = α.hom a
    rw [← AlgEquiv.ofInjective_apply i hi]
    exact congrArg Subtype.val (eqv.apply_symm_apply _)
  have hβφ : β.comp φ.hom = algebraMap K E := by
    ext k
    apply hi
    rw [RingHom.comp_apply, hiβ, ← RingHom.comp_apply, hαφ]
    exact (i.commutes k).symm
  refine ⟨Spec.map (CommRingCat.ofHom β) ≫ e.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom (algebraMap K E))
    congr 1
    ext x
    exact congrArg (fun f : K →+* E => f x) hβφ
  · change t = Spec.map (CommRingCat.ofHom i.toRingHom) ≫ _
    rw [← Category.assoc, ← Spec.map_comp]
    have hβα : CommRingCat.ofHom β ≫ CommRingCat.ofHom i.toRingHom = α := by
      ext x; exact hiβ x
    rw [hβα, hα, Category.assoc, e.hom_inv_id, Category.comp_id]

end GlobalTheory
