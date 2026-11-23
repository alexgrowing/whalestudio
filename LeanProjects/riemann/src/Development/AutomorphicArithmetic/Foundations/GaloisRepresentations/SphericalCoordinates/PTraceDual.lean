import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.traceDual_of :
    UpperTheory.Gal.W2.TraceDual := by
  intro F _ _ s hs
  classical
  let e := NumberField.RingOfIntegers.basis F
  choose m hm using fun k => hs (e k)
  let L : F →ₗ[ℚ] ℚ := (NumberField.integralBasis F).constr ℚ (fun k => (m k : ℚ))
  let D := (Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)
  let b : F := D.symm L
  have hb : ∀ x : F, Algebra.trace ℚ F (b * x) = L x := by
    intro x
    have h := LinearMap.congr_fun (D.apply_symm_apply L) x
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h
    exact h
  have htr : ∀ x : F, algebraMap ℚ ℂ (Algebra.trace ℚ F x) = ∑ τ : F →+* ℂ, τ x := by
    intro x
    rw [trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ (fun σ => rfl)
  have hk : ∀ k, ∑ τ : F →+* ℂ, τ (e k : F) * (τ b - s τ) = 0 := by
    intro k
    simp only [mul_sub, Finset.sum_sub_distrib, ← map_mul]
    rw [hm k, ← htr, mul_comm (e k : F) b, hb, sub_eq_zero]
    have he : (e k : F) = NumberField.integralBasis F k := by
      rw [NumberField.integralBasis_apply]
    rw [he, Module.Basis.constr_basis]
    simp
  let P : ((F →+* ℂ) → ℂ) →ₗ[ℂ] ℂ := ∑ τ, (τ b - s τ) • LinearMap.proj τ
  have hP : P = 0 := by
    apply (NumberField.canonicalEmbedding.latticeBasis F).ext
    intro k
    simp only [P, NumberField.canonicalEmbedding.latticeBasis_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply,
      NumberField.canonicalEmbedding.apply_at, smul_eq_mul, LinearMap.zero_apply]
    rw [← hk k]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_comm, NumberField.integralBasis_apply]
  refine ⟨b, fun τ => ?_⟩
  have h := LinearMap.congr_fun hP (Pi.single τ 1)
  simp [P, Pi.single_apply] at h
  rw [sub_eq_zero] at h
  exact h.symm
