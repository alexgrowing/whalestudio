import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteFibrePoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AbTorsionFiniteF

theorem finite_torsion_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} := by
  intro R _ _ D F _ _ _ k hk
  let g := jFK (R := R) F ≫ jK R
  let B' := (Over.pullback g).obj D.P.A
  have hB : IsAbelianScheme B' := GlobalTheory.isAbelianScheme_pullback_obj g D.P.A D.P.isAb
  have hfin := GlobalTheory.AbTorsionFinite.finite_torsion F B' hB k hk
  let φ : (TF (R := R) F ⟶ D.P.A) → (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ B') := fun x =>
    Over.homMk (pullback.lift x.left (𝟙_ (Over (Spec (CommRingCat.of F)))).hom
      ((Over.w x).trans (by simp [g]))) (pullback.lift_snd _ _ _)
  have hφ : ∀ x, (φ x).left ≫ pullback.fst D.P.A.hom g = x.left := fun x => pullback.lift_fst _ _ _
  have hpow : ∀ x : TF (R := R) F ⟶ D.P.A, (φ x) ^ k = 1 ↔ x ^ k = 1 := fun x =>
    GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull (by simp [g]) (isGrpPullback_pullback D.P.A g) (hφ x)
  refine Finite.of_injective (fun x : {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} =>
    (⟨φ x.1, (hpow x.1).2 x.2⟩ : {y : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ B' // y ^ k = 1})) ?_
  intro a b hab
  have e := congrArg (fun y => y.1.left ≫ pullback.fst D.P.A.hom g) hab
  simp only [hφ] at e
  exact Subtype.ext (Over.OverMorphism.ext e)

end GlobalTheory.AbTorsionFiniteF
