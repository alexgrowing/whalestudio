import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.EmbedQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.QzEnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.dualGen :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (r : ℕ), (∀ x : D, ∃ k : ℕ, (l : ℤ_[l]) ^ k • x = 0) → CardLe (Submodule.torsionBy ℤ_[l] D (l : ℤ_[l])) (l ^ r) →
      Tower.GenLE ℤ_[l] (D →ₗ[ℤ_[l]] QZ l) r := by
  intro l _ D _ _ r htors hcard
  classical
  obtain ⟨f, hf⟩ := embedQZ l D r htors hcard
  haveI := PropA.qzInj l
  refine ⟨Fintype.linearCombination ℤ_[l] (fun i => (LinearMap.proj i).comp f), ?_⟩
  intro φ
  obtain ⟨ψ, hψ⟩ := Module.Injective.out (R := ℤ_[l]) (Q := QZ l) f hf φ
  choose c hc using fun i => qzEnd l (ψ.comp (LinearMap.single ℤ_[l] (fun _ : Fin r => QZ l) i))
  refine ⟨c, ?_⟩
  ext d
  rw [Fintype.linearCombination_apply, ← hψ d]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  conv_rhs => rw [← Finset.univ_sum_single (f d)]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := hc i (f d i)
  simp only [LinearMap.comp_apply, LinearMap.single_apply] at h1
  exact h1.symm
