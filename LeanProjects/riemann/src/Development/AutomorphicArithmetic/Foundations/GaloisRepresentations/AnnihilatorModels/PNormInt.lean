import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.normInt_of :
    NormEx → SplitsBC → InjSplit → CoeffInt → LiftP → NormInt := by
  intro hNE hBC hIS hCI hLP l d R S _ _ _ h hcl ι _ s
  haveI hfin : Module.Finite R S := h.fin
  haveI het := h.et
  haveI : Module.Finite (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Module.FinitePresentation (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  haveI : Module.Flat (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Module.Projective (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨N', hN'⟩ := hNE (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) ι (fun k => 1 ⊗ₜ s k)
  obtain ⟨T, _, _, m, z, hinj, hz⟩ := hIS l d R S h
  letI : Algebra R T := ((algebraMap (Localization.Away (l : R)) T).comp (algebraMap R (Localization.Away (l : R)))).toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hNz := hN' T (Fin m) z hz
  have hint : ∀ i k, IsIntegral R (z i (1 ⊗ₜ s k)) := by
    intro i k
    have hs : IsIntegral R (s k) := Algebra.IsIntegral.isIntegral (R := R) (s k)
    have := hs.map (((z i).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] (Localization.Away (l : R) ⊗[R] S)))
    simpa using this
  have hco : ∀ (a : ℕ) (mm : ι →₀ ℕ), ∃ r, algebraMap R (Localization.Away (l : R)) r = MvPolynomial.coeff mm (N'.coeff a) := by
    intro a mm
    apply hcl
    have h1 := hCI R T ι (Fin m) (fun i k => z i (1 ⊗ₜ s k)) hint a mm
    rw [← hNz, Polynomial.coeff_map, MvPolynomial.coeff_map] at h1
    exact (isIntegral_algebraMap_iff hinj).1 h1
  obtain ⟨N, hN⟩ := hLP R (Localization.Away (l : R)) ι (algebraMap R (Localization.Away (l : R))) N' hco
  refine ⟨N, ?_⟩
  intro B _ _ hl I _ zB hzB
  letI : Algebra (Localization.Away (l : R)) B :=
    (IsLocalization.Away.lift (S := Localization.Away (l : R)) (l : R) (g := algebraMap R B) (by simpa using hl)).toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) B := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq (S := Localization.Away (l : R)) (l : R) (g := algebraMap R B) (by simpa using hl) r).symm
  obtain ⟨z', hz', hzz⟩ := hBC R (Localization.Away (l : R)) S B I zB hzB
  have h2 := hN' B I z' hz'
  simp only [hzz] at h2
  rw [← h2, ← hN]
  have hc : (MvPolynomial.map (algebraMap (Localization.Away (l : R)) B)).comp
      (MvPolynomial.map (σ := ι) (algebraMap R (Localization.Away (l : R)))) = MvPolynomial.map (algebraMap R B) := by
    ext x
    · simp [← IsScalarTower.algebraMap_apply]
    · simp
  simp only [mapP, Polynomial.map_map, hc]
