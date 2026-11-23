import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.SchGlue

theorem exists_glue_of_dense : ∀ {S X₀ : Scheme.{0}} {I : Type} (V X : I → Scheme.{0}) (κ : ∀ i, V i ⟶ S) (g : ∀ i, X i ⟶ V i)
    (B : I → I → Scheme.{0}) (a : ∀ i k, B i k ⟶ X i) (b : ∀ i k, B i k ⟶ X k) (j : ∀ i, X₀ ⟶ X i)
    (jB : ∀ i k, X₀ ⟶ B i k), (∀ i, IsOpenImmersion (κ i)) →
    (∀ i k, IsPullback (a i k) (b i k ≫ g k) (g i ≫ κ i) (κ k)) →
    (∀ i k, IsPullback (b i k) (a i k ≫ g i) (g k ≫ κ k) (κ i)) → (∀ i, IsReduced (X i)) →
    (∀ i, (X i).IsSeparated) → (∀ i, IsDominant (j i)) → (∀ i k, jB i k ≫ a i k = j i) →
    (∀ i k, jB i k ≫ b i k = j k) →
    ∃ (A : Scheme.{0}) (F : A ⟶ S) (ψ : ∀ i, X i ⟶ A),
      (∀ i, IsPullback (ψ i) (g i) F (κ i)) ∧ ∀ i k, IsPullback (a i k) (b i k) (ψ i) (ψ k) := by
  intro S X₀ I V X κ g B a b j jB hκ ha hb hred hsep hdom hja hjb
  have oa : ∀ i k, IsOpenImmersion (a i k) := fun i k =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (ha i k).flip (hκ k)
  have w : ∀ i k, a i k ≫ g i ≫ κ i = b i k ≫ g k ≫ κ k := fun i k => by
    simpa using (ha i k).w
  refine GlobalTheory.CocycleGlue.exists_glue V X κ hκ g B a b ha hb ?_
  intro i j' k T x y z hxy hxz
  let P := pullback (a i j') (a i k)
  haveI : IsReduced P := isReduced_of_isOpenImmersion (pullback.fst (a i j') (a i k) ≫ a i j')
  obtain ⟨u, hu⟩ : ∃ u : P ⟶ B j' k, u ≫ a j' k = pullback.fst _ _ ≫ b i j' :=
    ⟨(ha j' k).lift (pullback.fst _ _ ≫ b i j') (pullback.snd _ _ ≫ b i k ≫ g k)
      (by simp only [Category.assoc, ← w]; rw [pullback.condition_assoc]), (ha j' k).lift_fst _ _ _⟩
  let e : X₀ ⟶ P := pullback.lift (jB i j') (jB i k) (by rw [hja, hja])
  haveI : IsDominant (e ≫ pullback.fst (a i j') (a i k) ≫ a i j') := by
    have : e ≫ pullback.fst (a i j') (a i k) ≫ a i j' = j i := by
      simp only [e, pullback.lift_fst_assoc, hja]
    rw [this]; exact hdom i
  haveI : IsDominant e :=
    IsDominant.of_comp_of_isOpenImmersion e (pullback.fst (a i j') (a i k) ≫ a i j')
  have heu : e ≫ u = jB j' k := by
    rw [← cancel_mono (a j' k), Category.assoc, hu, hja]
    simp only [e, pullback.lift_fst_assoc, hjb]
  have hub : u ≫ b j' k = pullback.snd _ _ ≫ b i k := by
    haveI := hsep k
    refine ext_of_isDominant e ?_
    rw [← Category.assoc, heu, hjb]
    simp only [e, pullback.lift_snd_assoc, hjb]
  have hy : y = pullback.lift x z hxz ≫ u := by
    rw [← cancel_mono (a j' k), Category.assoc, hu, ← hxy, pullback.lift_fst_assoc]
  rw [hy, Category.assoc, hub, pullback.lift_snd_assoc]

end GlobalTheory.SchGlue
