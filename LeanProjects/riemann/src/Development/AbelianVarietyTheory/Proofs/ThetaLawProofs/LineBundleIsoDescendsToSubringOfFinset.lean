import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem exists_finset_lbIso_adjoin {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    {B : Scheme.{0}} (pB : B ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] (M N : LB B)
    (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (pullback.fst pB (spMap (algebraMap k A))))
      (N.pull (pullback.fst pB (spMap (algebraMap k A))))) :
    ∃ s : Finset A,
      LBIso (M.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))))
        (N.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A)))))) := by
  classical
  obtain ⟨t, f, h⟩ := exists_lbIso_of_isLimit (Spread.bcDiagram pB A)
    (X := pullback pB (spMap (algebraMap k A)))
    (fun s => Spread.bcMap pB (Algebra.adjoin k (s.unop : Set A)).val)
    (fun f => (Spread.bcCone pB A).w f) (Spread.isLimitBcCone pB A) (i := .op ∅)
    (M.pull (pullback.fst _ _)) (N.pull (pullback.fst _ _)) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.chartPull
      (chartPullOut M _ _ _ _ fun _ => (Spread.bcMap_fst pB _).symm)
      (chartPullOut N _ _ _ _ fun _ => (Spread.bcMap_fst pB _).symm) H)
  have H₂ := LBIso.chartPull (chartPullIn M _ _ _) (chartPullIn N _ _ _) h
  refine ⟨t.unop, ?_⟩
  exact LBIso.chartPull (chartPullSame M _ _ _ (𝟙 _) fun _ =>
      ((Category.id_comp _).trans (Spread.bcMap_fst pB _)).symm)
    (chartPullSame N _ _ _ (𝟙 _) fun _ =>
      ((Category.id_comp _).trans (Spread.bcMap_fst pB _)).symm) H₂

theorem lbIso_descends_to_subring_containing_finset :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (M N : LB X₀), IsPullback π f f₀ (spMap R₀.subtype) → M.IsLB → N.IsLB → LBIso (M.pull π) (N.pull π) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → LBIso (M.pull π₁) (N.pull π₁) := by
  intro S _ R₀ X X₀ f f₀ π _ _ M N hp hM hN H
  have same : ∀ {Y Y' : Scheme.{0}} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀), a' = j ≫ a →
      LBIso (M.pull a) (N.pull a) → LBIso (M.pull a') (N.pull a') := fun a j a' e h =>
    LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h
  have hp' : IsPullback π f f₀ (spMap (algebraMap R₀ S)) := hp
  have H₁ := same π hp'.isoPullback.inv (pullback.fst f₀ (spMap (algebraMap R₀ S)))
    (IsPullback.isoPullback_inv_fst hp').symm H
  obtain ⟨s, H₂⟩ := exists_finset_lbIso_adjoin f₀ M N hM hN H₁
  refine ⟨s, fun R₁ h hs X₁ f₁ π₁ hp₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let g : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hg : spMap g ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let m : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S)))) :=
    pullback.lift π₁ (f₁ ≫ spMap g) (by rw [Category.assoc, hg, hp₁.w])
  exact same _ m π₁ (pullback.lift_fst _ _ _).symm H₂

end GlobalTheory
