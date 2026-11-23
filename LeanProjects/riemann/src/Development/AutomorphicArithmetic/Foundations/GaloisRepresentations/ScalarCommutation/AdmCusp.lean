import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSliceAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateEigenSubDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldedEqOrbitalReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbUEqZeroOfCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwahoriRegularSplit

theorem UpperTheory.Gal.Spc.cuspIrr_kFinite_rep_eq_centralCuspForm :
    UpperTheory.Gal.Spc.AdmCusp := by
  intro X _ k _ _ _ _ _ _ _ n Ty hJo hJc hker hcusp f hf h hh
  have hform : ∀ g, f (Ty.L.loc g * h) = UpperTheory.Gal.W2.Seed.tyFn Ty.J Ty.ψ g * f h := by
    intro g
    unfold UpperTheory.Gal.W2.Seed.tyFn
    split_ifs with hg
    · rw [Ty.L.comm g h hh]
      exact hf.2.2 ⟨g, hg⟩ h
    · rw [zero_mul]
      by_contra hne
      apply hg
      have hmem := hf.2.1 _ hne
      rwa [map_mul, Ty.L.pr_loc, hh, mul_one] at hmem
  have hTC : GlobalTheory.Block5c.TypeCusp := GlobalTheory.typeFunction_constantTerm_eq_zero
  have hT := hTC k (Fin n) Ty.J hJo hJc Ty.ψ hker
    (fun a b e ha hb u hu h₀ =>
      UpperTheory.Gal.Spc.typeSlice k n Ty.J hJo hJc Ty.ψ hker hcusp a b e ha hb u hu h₀)
    (UpperTheory.Gal.W2.Seed.tyFn Ty.J Ty.ψ)
    (fun g hg => by simp [UpperTheory.Gal.W2.Seed.tyFn, hg])
    (fun g hg => by simp [UpperTheory.Gal.W2.Seed.tyFn, hg])
  intro a b ε ha hb μ hμ u hu g₀ h₀
  have hz := hT.2.2.2 a b ε ha hb μ hμ u hu g₀ h₀
  simp_rw [hform]
  rw [MeasureTheory.integral_mul_const, hz, zero_mul]
