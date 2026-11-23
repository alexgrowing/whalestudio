import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr

namespace GlobalTheory.ShFam.GalCarry.Corr

open Limits

theorem exists_hom_of_extends (F : Type) [Field F] (Y Y' : Var F) (p' : Sp Y.Fn ⟶ Y'.X)
    (hp : p' ≫ Y'.str = genericPt Y ≫ Y.str)
    (hl : ∀ y : Y.X, ∃ l : Sp (Y.X.presheaf.stalk y) ⟶ Y'.X,
      spMap (algebraMap (Y.X.presheaf.stalk y) Y.Fn) ≫ l = p') :
    ∃ φ : Y.X ⟶ Y'.X, genericPt Y ≫ φ = p' ∧ φ ≫ Y'.str = Y.str := by
  have hsep : Y'.X.IsSeparated := ⟨by rw [← terminal.comp_from Y'.str]; infer_instance⟩
  have hdom : IsDominant (Y.X.fromSpecStalk (genericPoint Y.X)) := ⟨by
    refine Dense.mono ?_ (dense_iff_closure_eq.2 (genericPoint_spec Y.X))
    rintro _ rfl
    exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩⟩

  have hcan : ∀ (y : Y.X) (a b : Sp (Y.X.presheaf.stalk y) ⟶ Sp F),
      spMap (algebraMap (Y.X.presheaf.stalk y) Y.Fn) ≫ a =
        spMap (algebraMap (Y.X.presheaf.stalk y) Y.Fn) ≫ b → a = b := by
    intro y a b hab
    rw [← Spec.map_preimage a, ← Spec.map_preimage b] at hab ⊢
    simp only [spMap, ← Spec.map_comp] at hab
    congr 1
    ext z
    have := congrArg (fun g => g.hom z) (Spec.map_injective hab)
    exact FaithfulSMul.algebraMap_injective (Y.X.presheaf.stalk y) Y.Fn this
  have hspec : ∀ y : Y.X, spMap (algebraMap (Y.X.presheaf.stalk y) Y.Fn) ≫ Y.X.fromSpecStalk y =
      genericPt Y :=
    fun y => Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y.X).specializes trivial)
  let f : Y.X ⤏ Y'.X := Scheme.RationalMap.ofFunctionField Y.str Y'.str p' hp
  have hfF : f.fromFunctionField = p' := Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have htop : f.domain = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨l, hl1⟩ := hl y
    have h2 : l ≫ Y'.str = Y.X.fromSpecStalk y ≫ Y.str := by
      apply hcan y
      rw [← Category.assoc, hl1, hp, ← Category.assoc, hspec]
    refine Scheme.RationalMap.mem_domain.2 ⟨Scheme.PartialMap.ofFromSpecStalk (x := y) Y.str Y'.str l h2,
      Scheme.PartialMap.mem_domain_ofFromSpecStalk (x := y) Y.str Y'.str l h2, ?_⟩
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap, hfF, ← hl1]
    have hm := Scheme.PartialMap.mem_domain_ofFromSpecStalk (x := y) Y.str Y'.str l h2
    have e1 : spMap (algebraMap (Y.X.presheaf.stalk y) Y.Fn) ≫
        (Scheme.PartialMap.ofFromSpecStalk (x := y) Y.str Y'.str l h2).fromSpecStalkOfMem hm =
        (Scheme.PartialMap.ofFromSpecStalk (x := y) Y.str Y'.str l h2).fromFunctionField := by
      simp only [Scheme.PartialMap.fromSpecStalkOfMem]
      rw [← Category.assoc]
      congr 1
      rw [← cancel_mono (Scheme.PartialMap.ofFromSpecStalk (x := y) Y.str Y'.str l h2).domain.ι,
        Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact hspec y
    rw [← e1, Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
  let k : Y.X ⟶ f.domain.toScheme := IsOpenImmersion.lift f.domain.ι (𝟙 Y.X)
    (by rw [Scheme.Opens.range_ι, htop]; simp)
  have hk : k ≫ f.domain.ι = 𝟙 Y.X := IsOpenImmersion.lift_fac _ _ _
  have hm : genericPoint Y.X ∈ f.toPartialMap.domain := by
    change _ ∈ f.domain
    rw [htop]; trivial
  have hm' : genericPoint Y.X ∈ f.domain := by rw [htop]; trivial
  have e2 : genericPt Y ≫ k = f.domain.fromSpecStalkOfMem _ hm' := by
    rw [← cancel_mono f.domain.ι, Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, hk,
      Category.comp_id]
    rfl
  have hg : genericPt Y ≫ (k ≫ f.toPartialMap.hom) = p' := by
    calc genericPt Y ≫ (k ≫ f.toPartialMap.hom) = f.toPartialMap.fromSpecStalkOfMem hm := by
          exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f.toPartialMap.hom) e2)
      _ = f.toPartialMap.fromFunctionField := rfl
      _ = p' := by
          rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
            Scheme.RationalMap.toRationalMap_toPartialMap, hfF]
  refine ⟨k ≫ f.toPartialMap.hom, hg, ?_⟩
  apply ext_of_isDominant (Y.X.fromSpecStalk (genericPoint Y.X))
  change genericPt Y ≫ (k ≫ f.toPartialMap.hom) ≫ Y'.str = genericPt Y ≫ Y.str
  rw [← Category.assoc, hg, hp]

end GlobalTheory.ShFam.GalCarry.Corr
