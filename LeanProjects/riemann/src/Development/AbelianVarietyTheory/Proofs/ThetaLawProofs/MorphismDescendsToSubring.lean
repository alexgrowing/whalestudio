import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem morphism_descends_to_subring :
    ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X X₀ Y₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp R₀) (q : Y₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation q] (φ : X ⟶ Y₀), IsPullback π f f₀ (spMap R₀.subtype) → φ ≫ q = π ≫ f₀ → ∃ S : Finset R, ∀ (R₁ : Subring R) (h : R₀ ≤ R₁), (S : Set R) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Y₀, j ≫ ψ = φ ∧ ψ ≫ q = π₁ ≫ f₀ := by
  intro R _ R₀ X X₀ Y₀ f f₀ q π _ _ _ φ hP hφ
  let _ : Algebra R₀ R := R₀.subtype.toAlgebra
  have hP' : IsPullback π f f₀ (spMap (algebraMap R₀ R)) := hP

  let e := hP'.isoPullback
  obtain ⟨R', ψ', hfg, hψ'q, hψ'φ⟩ := Spread.exists_fg_comp_eq (pB := f₀) (pZ := q) (A := R)
    (e.inv ≫ φ) (by rw [Category.assoc, hφ, ← Category.assoc, hP'.isoPullback_inv_fst])
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun R₁ h hS X₁ f₁ π₁ j hP₁ hjπ hjf => ?_⟩

  have hle : ∀ x ∈ R', x ∈ R₁ := by
    let T : Subalgebra R₀ R := { R₁.toSubsemiring with algebraMap_mem' := fun r => h r.2 }
    have hT : R' ≤ T := ht ▸ Algebra.adjoin_le hS
    exact fun x hx => hT hx
  let a : R' →+* R₁ := RingHom.codRestrict R'.val.toRingHom R₁ (fun x => hle x x.2)
  have ha : spMap a ≫ spMap (algebraMap R₀ R') = spMap (Subring.inclusion h) := by
    rw [spMap_comp_moduli_spaces]
    congr 1
  have hb : spMap R₁.subtype ≫ spMap a = spMap R'.val.toRingHom := by
    rw [spMap_comp_moduli_spaces]
    congr 1
  let L : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ R')) :=
    pullback.lift π₁ (f₁ ≫ spMap a) (by rw [Category.assoc, ha]; exact hP₁.w)
  refine ⟨L ≫ ψ', ?_, ?_⟩
  · have hjL : j ≫ L = e.hom ≫ Spread.bcMap f₀ R'.val := by
      apply pullback.hom_ext
      · simp only [L, e, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst]
        rw [pullback.lift_fst, hjπ]
      · simp only [L, e, Category.assoc, pullback.lift_snd, Spread.bcMap_snd,
          IsPullback.isoPullback_hom_snd_assoc]
        rw [← Category.assoc, hjf, Category.assoc, hb]
    rw [← Category.assoc, hjL, Category.assoc, hψ'φ, ← Category.assoc, e.hom_inv_id,
      Category.id_comp]
  · rw [Category.assoc, hψ'q, ← Category.assoc, pullback.lift_fst]

end GlobalTheory
