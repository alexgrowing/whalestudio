import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Stabiliser

theorem comp_eq_iff_range_subset {S : Scheme.{0}} {T X Z : Over S} [IsReduced T.left]
    [IsSeparated Z.hom] (f g : X ⟶ Z) (x : T ⟶ X) :
    x ≫ f = x ≫ g ↔ Set.range x.left ⊆ Set.range (equalizer.ι f g).left := by
  constructor
  · intro h
    rintro _ ⟨t, rfl⟩
    refine ⟨(equalizer.lift x h).left t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · intro h
    have hs : Surjective (pullback.fst x.left (equalizer.ι f g).left) := by
      refine ⟨Set.range_eq_univ.1 ?_⟩
      rw [Scheme.Pullback.range_fst]
      exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩
    have hc : (equalizer.ι f g).left ≫ f.left = (equalizer.ι f g).left ≫ g.left :=
      congrArg CommaMorphism.left (equalizer.condition f g)
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Z.hom
      ((Over.w _).trans (Over.w _).symm) (pullback.fst x.left (equalizer.ι f g).left) ?_)
    rw [Over.comp_left, Over.comp_left, pullback.condition_assoc, pullback.condition_assoc, hc]

def stab {S : Scheme.{0}} {B Z : Over S} [GrpObj B] (φ : B ⟶ Z) : Subgroup (𝟙_ (Over S) ⟶ B) :=
  have key : ∀ a b : 𝟙_ (Over S) ⟶ B, (toUnit B ≫ (b * a)) * 𝟙 B =
      ((toUnit B ≫ a) * 𝟙 B) ≫ ((toUnit B ≫ b) * 𝟙 B) := fun a b => by
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      toUnit_unique (_ ≫ toUnit B) (toUnit B), _root_.mul_assoc]
  have one : (toUnit B ≫ (1 : 𝟙_ (Over S) ⟶ B)) * 𝟙 B = 𝟙 B := by
    rw [MonObj.comp_one, _root_.one_mul]
  { carrier := {x | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}
    mul_mem' := fun {a b} ha hb => by
      rw [Set.mem_ofPred_eq] at ha hb ⊢
      rw [key, Category.assoc, ha, hb]
    one_mem' := by rw [Set.mem_ofPred_eq, one, Category.id_comp]
    inv_mem' := fun {a} ha => by
      rw [Set.mem_ofPred_eq] at ha ⊢
      conv_lhs => rw [← ha]
      rw [← Category.assoc, ← key, mul_inv_cancel, one, Category.id_comp] }

theorem exists_closed_stabiliser : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] (φ : B ⟶ Z), ∃ (C : Subgroup (𝟙_ _ ⟶ B)) (W : Set B.left), IsClosed W ∧ (∀ x, x ∈ C ↔ ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ) ∧ ∀ x, x ∈ C ↔ Set.range x.left ⊆ W := by
  intro K _ _ B _ _ hB Z _ φ
  have := hB.smooth
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have : IsReduced (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  refine ⟨stab φ, ⋂ z : 𝟙_ _ ⟶ B, Set.range
    (equalizer.ι ((𝟙 B * (toUnit B ≫ z)) ≫ φ) (toUnit B ≫ z ≫ φ)).left,
    isClosed_iInter fun z => (Scheme.Hom.isClosedEmbedding _).isClosed_range,
    fun _ => Iff.rfl, fun x => ?_⟩
  have e₁ : ∀ z : 𝟙_ _ ⟶ B, x ≫ (𝟙 B * (toUnit B ≫ z)) ≫ φ = z ≫ ((toUnit B ≫ x) * 𝟙 B) ≫ φ := by
    intro z
    simp only [← Category.assoc, MonObj.comp_mul, Category.comp_id]
    rw [toUnit_unique (x ≫ toUnit B) (𝟙 _), toUnit_unique (z ≫ toUnit B) (𝟙 _),
      Category.id_comp, Category.id_comp]
  have e₂ : ∀ z : 𝟙_ _ ⟶ B, x ≫ toUnit B ≫ z ≫ φ = z ≫ φ := by
    intro z
    rw [← Category.assoc, toUnit_unique (x ≫ toUnit B) (𝟙 _), Category.id_comp]
  rw [Set.subset_iInter_iff]
  simp only [← comp_eq_iff_range_subset, e₁, e₂]
  refine ⟨fun h z => congrArg (z ≫ ·) h, fun h => ?_⟩
  refine Over.OverMorphism.ext (GlobalTheory.ComplexPoints.hom_ext_of_points B.hom Z.hom
    ((Over.w _).trans (Over.w _).symm) fun y hy => ?_)
  exact congrArg CommaMorphism.left (h (Over.homMk y hy))

end GlobalTheory.Stabiliser
