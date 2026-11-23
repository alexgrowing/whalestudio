import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureComponentTrdegGeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfIndependentAndTangentBoundStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpensStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem finiteType_of_isQProjOver_affineOpen {o : Type} [CommRing o] {X : Scheme.{0}} {s : X ⟶ Sp o}
    (hs : IsQProjOver s) (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X) [IsOpenImmersion x]
    (hx : x ≫ s = spMap (algebraMap o R)) : Algebra.FiniteType o R := by
  obtain ⟨N, i, hi, -, rfl⟩ := hs
  have := isProper_str o N
  have h : LocallyOfFiniteType (spMap (algebraMap o R)) := by
    rw [← hx]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  exact RingHom.finiteType_algebraMap.mp h

theorem ThetaFam.smooth_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → (∀ (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  intro h1 h2 g n N' J Mat κ w w' o _ b em C d F hb hC ht
  have : IsDedekindDomain o := hb.1
  refine GlobalTheory.T.smooth_genericFibre_of_affine_opens o F.MM F.s d fun R _ _ x hx hxs => ?_
  exact GlobalTheory.T.smooth_genericFibre_of_independent_and_tangent_bound o em R d hb.2.2 (finiteType_of_isQProjOver_affineOpen F.qproj R x hxs)
    (GlobalTheory.T.thetaClosure_component_trdeg_ge h1 h2 n g N' J Mat κ w w' o b em C d F hb hC R x hx hxs)
    (fun he => ht R x hx hxs he)

end GlobalTheory.ZM
