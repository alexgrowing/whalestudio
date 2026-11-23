import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSeparableCompositum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory

theorem splitFibre_of_isOpenImmersion {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsOpenImmersion f] (G : Over Z) [GrpObj G]
    (G' : Over Y) [GrpObj G'] (φ : G'.left ⟶ G.left) (hφ : IsGrpPullback G' G f φ) (h : SplitFib G') (y : Y) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField (f y)) k), FiniteDimensional (Z.residueField (f y)) k ∧
      Algebra.IsSeparable (Z.residueField (f y)) k ∧ ∃ S : SplitExt (Sp k),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫
          Z.fromSpecResidueField (f y))).obj G) := by
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := h y
  let ε : Z.residueField (f y) ≃+* Y.residueField y := (asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv
  let A : Algebra (Z.residueField (f y)) k :=
    ((algebraMap (Y.residueField y) k).comp (f.residueFieldMap y).hom).toAlgebra
  have hc : (algebraMap (Z.residueField (f y)) k).comp (ε.symm : Y.residueField y →+* Z.residueField (f y)) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (Y.residueField y) k) := by
    ext a
    exact congrArg (algebraMap (Y.residueField y) k) (ε.apply_symm_apply a)
  refine ⟨k, inferInstance, A, Module.Finite.of_equiv_equiv ε.symm (RingEquiv.refl k) hc,
    Algebra.IsSeparable.of_equiv_equiv ε.symm (RingEquiv.refl k) hc, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Y.fromSpecResidueField y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫ Z.fromSpecResidueField (f y) := by
    have a₁ : Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Spec.map (f.residueFieldMap y) := by
      rw [← Spec.map_comp]
      rfl
    rw [a₁, Category.assoc, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← key]
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y)).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₀ := isGt_of_iso ((Over.pullback _).mapIso e) hGt
  have : IsMonHom (pullCompIso (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y) f G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  exact isGt_of_iso (pullCompIso _ f G).symm h₀

theorem splitFib_of_openCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, SplitFib (u i).G) → SplitFib t.G := by
  intro E _ _ _ H Z t I Y f u m ho hc hs z
  obtain ⟨i, y, rfl⟩ := hc z
  have := ho i
  exact splitFibre_of_isOpenImmersion (f i) t.G (u i).G _ (m i).cart (hs i) y

end GlobalTheory
