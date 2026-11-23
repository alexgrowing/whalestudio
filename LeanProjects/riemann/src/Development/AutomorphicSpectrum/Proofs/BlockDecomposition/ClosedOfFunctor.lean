import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalPropertyAffineIdealCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineIdealLocusCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusLocalToGlobalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperIntegralPerfectFamilyExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricallyIntegralGlobalFunctionsConstantStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem closed_of_functor (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    (near : ∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)) (I : Ideal Γ(Y, U)), y ∈ Y.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g r) →
        (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g)) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ Y), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ ∃ z : T ⟶ Z, z ≫ i = t :=
  GlobalTheory.T.affine_ideal_locus_criterion Y P stab loc (GlobalTheory.T.local_property_affine_ideal_criterion Y P stab loc near)

theorem locus_near {S : Scheme.{0}} {A Y : Over S} [GrpObj A] (hA : IsAbelianScheme A) [IsLocallyNoetherian Y.left]
    {N : LB (A ⊗ Y).left} (hN : N.IsLB) (y : Y.left) :
    ∃ (U : Y.left.Opens) (hU : IsAffineOpen U) (r : Γ(Y.left, U)) (I : Ideal Γ(Y.left, U)), y ∈ Y.left.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y.left, U) →+* R'), IsUnit (g r) →
        (Locus N (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  obtain ⟨p, hp⟩ := hU.range_fromSpec.ge hy
  have : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨X, f, M, hM, h₁, h₂, h₃, h₄, h₅, h₆, H⟩ := GlobalTheory.T.proper_integral_perfect_family_exists S A Y hA N hN Γ(Y.left, U) hU.fromSpec
  obtain ⟨r, I, hr, H'⟩ := GlobalTheory.T.geometrically_integral_global_functions_constant _ X f M hM h₁ h₂ h₃ h₄ h₅ h₆ p
  refine ⟨U, hU, r, I, ?_, fun R' _ g hg => ?_⟩
  · rw [← hU.fromSpec_image_basicOpen]
    exact ⟨p, hr, hp⟩
  · have hq := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))
    exact (H R' g _ _ _ hq).symm.trans (H' R' g _ _ _ hq hg)

theorem trivLocus : TrivLocus := by
  intro S A Y _ hA hY N hN h1
  obtain ⟨Z, i, hi, H⟩ := closed_of_functor Y.left (fun T t => Locus N t)
    (fun T T' h t ht => ht.comp h) (fun T t h => GlobalTheory.T.trivial_locus_local_to_global S A Y hA N hN h1 T t h) (locus_near hA hN)
  refine ⟨Over.mk (i ≫ Y.hom), Over.homMk i rfl, hi, fun T y => ?_⟩
  refine (locus_left_iff y).symm.trans ((H _ y.left).trans ⟨?_, ?_⟩)
  · rintro ⟨z, hz⟩
    exact ⟨Over.homMk z (by simp [reassoc_of% hz]), by ext; simpa using hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z.left, by simpa using congrArg (fun q => q.left) hz⟩

end GlobalTheory.CompanionTheory.TrivLoc
