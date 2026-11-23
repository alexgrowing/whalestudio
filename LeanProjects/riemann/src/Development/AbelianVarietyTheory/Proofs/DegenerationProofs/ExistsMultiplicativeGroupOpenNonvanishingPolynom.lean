import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

noncomputable section
namespace GlobalTheory.SS.TorOpen
open GlobalTheory.SplitTorus ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem isIso_univPt_left (k : Type) [CommRing k] (X : Type) [AddCommGroup X] :
    IsIso (univPt (A := CommRingCat.of k) X (𝟙 (Sp k))).left := by
  have h1 := GlobalTheory.Diag.isPullback_groupRing k X
  have h2 := GlobalTheory.Diag.isPullback_torusFst (Sp k) X
  have e : (univPt (A := CommRingCat.of k) X (𝟙 (Sp k))).left = (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · refine Eq.trans ?_ (IsPullback.isoIsPullback_hom_fst _ _ h1 h2).symm
      refine (pullback.lift_fst _ _ _).trans ?_
      rw [Spec.map_comp]
      exact toSpecΓ_SpecMap_ΓSpecIso_inv_assoc (torusRing (CommRingCat.of k) X) _
    · refine Eq.trans ?_ (IsPullback.isoIsPullback_hom_snd _ _ h1 h2).symm
      exact (Over.w _).trans (Category.comp_id _)
  rw [e]; infer_instance

theorem exists_ringHom (k : Type) [Field k] (q : Polynomial k) :
    ∃ ψ : AddMonoidAlgebra k (ULift.{0} ℤ) →+* Localization.Away (Polynomial.X * q),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ)) ∧
      ψ.comp (algebraMap k _) = algebraMap k _ ∧
      ψ (AddMonoidAlgebra.single (ULift.up 1) 1) = algebraMap (Polynomial k) _ Polynomial.X := by
  let L := Localization.Away (Polynomial.X * q)
  have hu : IsUnit (algebraMap (Polynomial k) L Polynomial.X) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := L) (Polynomial.X * q)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  let ψ' : LaurentPolynomial k →+* L := IsLocalization.Away.lift (Polynomial.X : Polynomial k) hu
  have hψ : ψ'.comp (algebraMap (Polynomial k) _) = algebraMap _ _ :=
    IsLocalization.Away.lift_comp _ hu
  let e : AddMonoidAlgebra k (ULift.{0} ℤ) ≃ₐ[k] LaurentPolynomial k :=
    AddMonoidAlgebra.domCongr k k AddEquiv.ulift
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ')) := by
    have a1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k)))) :=
      IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial k)
    have a2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ') ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k)))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      exact IsOpenImmersion.of_isLocalization (Polynomial.X * q)
    exact IsOpenImmersion.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k))))
  refine ⟨ψ'.comp e.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) := e.toRingEquiv.toCommRingCatIso.isIso_hom
    infer_instance
  · ext c
    have : e (algebraMap k _ c) = algebraMap (Polynomial k) _ (algebraMap k _ c) := by
      rw [e.commutes]; simp
    change ψ' (e (algebraMap k _ c)) = _
    rw [this, ← RingHom.comp_apply, hψ, ← IsScalarTower.algebraMap_apply]
  · have : e (AddMonoidAlgebra.single (ULift.up 1) 1) = algebraMap (Polynomial k) _ Polynomial.X := by
      simp [e]; rfl
    change ψ' (e _) = _
    rw [this, ← RingHom.comp_apply, hψ]

theorem exists_of_ringHom (k L : Type) [CommRing k] [CommRing L] [Algebra k L]
    (ψ : AddMonoidAlgebra k (ULift.{0} ℤ) →+* L)
    (h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))) (h2 : ψ.comp (algebraMap k _) = algebraMap k _)
    (t : L) (h3 : ψ (AddMonoidAlgebra.single (ULift.up 1) 1) = t) :
    ∃ jj : algOver k L ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : L →ₐ[k] k,
      (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x t * y t = z t := by
  have hs : Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap k _))) ≫ 𝟙 (Sp k) =
      spMap (algebraMap k L) := by
    rw [h2]; exact Category.comp_id _
  let jj : algOver k L ⟶ Gm (Sp k) :=
    ptOf (A := CommRingCat.of k) (B := CommRingCat.of L) (𝟙 (Sp k)) ψ hs
  refine ⟨jj, ?_, fun x y z h => ?_⟩
  · have := isIso_univPt_left k (ULift.{0} ℤ)
    exact IsOpenImmersion.comp (Spec.map (CommRingCat.ofHom ψ))
      (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left
  · have key : ∀ w : L →ₐ[k] k,
        pull (B := CommRingCat.of k) (s := spMap (algebraMap k k)) (algOverHom w ≫ jj)
          (chi _ (ULift.up 1)) = w t := by
      intro w
      have hs' : Spec.map (CommRingCat.ofHom (((w : L →+* k).comp ψ).comp (algebraMap k _))) ≫ 𝟙 (Sp k) =
          spMap (algebraMap k k) := by
        rw [RingHom.comp_assoc, h2, w.comp_algebraMap]; exact Category.comp_id _
      have e : algOverHom w ≫ jj = ptOf (A := CommRingCat.of k) (B := CommRingCat.of k) (𝟙 (Sp k))
          ((w : L →+* k).comp ψ) hs' := by
        ext1
        change Spec.map (CommRingCat.ofHom (w : L →+* k)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫
            (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left =
          Spec.map (CommRingCat.ofHom ((w : L →+* k).comp ψ)) ≫
            (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left
        rw [← Category.assoc, ← Spec.map_comp]
        rfl
      rw [e, pull_ptOf, ev_chi]
      exact congrArg w h3
    rw [← key, ← key, ← key, ← h]
    exact (pull_mul_chi (B := CommRingCat.of k) (s := spMap (algebraMap k k)) _ _ _).symm

theorem exists_open_part : ∀ (k : Type) [Field k] (q : Polynomial k), ∃ jj : algOver k (Localization.Away (Polynomial.X * q)) ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : Localization.Away (Polynomial.X * q) →ₐ[k] k, (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x (algebraMap (Polynomial k) _ Polynomial.X) * y (algebraMap (Polynomial k) _ Polynomial.X) = z (algebraMap (Polynomial k) _ Polynomial.X) := by
  intro k _ q
  obtain ⟨ψ, h1, h2, h3⟩ := exists_ringHom k q
  exact exists_of_ringHom k _ ψ h1 h2 _ h3

end GlobalTheory.SS.TorOpen
end
