import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTranslateCoefficientsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompProdOfFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InfTranslPts

theorem factor_fst {S K : Type} [CommRing S] [Field K] (w : Sp K ⟶ Sp (DualNumber S)) :
    w = (w ≫ spMap (algebraMap S (DualNumber S))) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective w
  have hε : ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
    have h : ψ.hom (DualNumber.eps : DualNumber S) * ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 h
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun x => ?_
  change ψ.hom x = ψ.hom (algebraMap S (DualNumber S) x.fst)
  have hx : x = algebraMap S (DualNumber S) x.fst + algebraMap S (DualNumber S) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, hε, mul_zero, add_zero]

theorem transl_field_point {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
    (P : tEpsG x0 ⟶ G)
    (hP : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ G).left)
    {K : Type} [Field K] (z : Sp K ⟶ (tEpsG x0 ⊗ G).left) :
    z ≫ (lift (fst (tEpsG x0) G ≫ P) (snd (tEpsG x0) G) ≫ μ[G]).left = z ≫ (snd (tEpsG x0) G).left := by
  let zz : Over.mk (z ≫ (tEpsG x0 ⊗ G).hom) ⟶ tEpsG x0 ⊗ G := Over.homMk z rfl
  let p : tEpsG x0 ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : GlobalTheory.VertSpanZero.redOver x0 ≫ P = 1 := Over.OverMorphism.ext hP
  have h2 : zz ≫ fst (tEpsG x0) G = (zz ≫ fst (tEpsG x0) G ≫ p) ≫ GlobalTheory.VertSpanZero.redOver x0 := by
    apply Over.OverMorphism.ext
    have := factor_fst (S := S) (K := K) (z ≫ (fst (tEpsG x0) G).left)
    exact this
  have h3 : zz ≫ fst (tEpsG x0) G ≫ P = 1 := by
    rw [← Category.assoc, h2, Category.assoc, h1, MonObj.comp_one]
  have h4 : zz ≫ ((fst (tEpsG x0) G ≫ P) * snd (tEpsG x0) G) = zz ≫ snd (tEpsG x0) G := by
    rw [MonObj.comp_mul, h3, _root_.one_mul]
  exact congrArg (fun q => q.left) h4

theorem transl_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  intro E _ _ _ H X t S _ x0 P hP y
  refine ⟨(tEpsG x0 ⊗ t.G).left.residueField y, inferInstance,
    (tEpsG x0 ⊗ t.G).left.fromSpecResidueField y, ?_, transl_field_point t.G x0 P hP _⟩
  exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply y _⟩

end GlobalTheory.InfTranslPts
