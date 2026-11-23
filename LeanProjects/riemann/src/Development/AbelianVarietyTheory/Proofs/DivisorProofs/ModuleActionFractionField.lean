import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_fibre_generator_basis : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M]
    (K : Type) [Field K] [Algebra R K],
    (∀ k : K, ∃ a s : R, algebraMap R K s ≠ 0 ∧ algebraMap R K s * k = algebraMap R K a) →
    ∀ (N : Type) [AddCommGroup N] [Module K N] [Module O N] [SMulCommClass K O N]
    (e : K ⊗[R] M ≃ₗ[K] N),
    (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    (letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module;
      Module.Invertible (K ⊗[ℤ] O) N) →
    ∃ m : M, Function.Bijective
      (Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m))) := by
  intro R O _ _ J _ b M _ _ _ _ K _ _ hfrac N _ _ _ _ e he hinv
  letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module
  let B := Algebra.TensorProduct.basis K b
  haveI : Module.Finite K (K ⊗[ℤ] O) := Module.Finite.of_basis B
  haveI : IsArtinianRing (K ⊗[ℤ] O) := IsArtinianRing.of_finite K _
  haveI : Finite (MaximalSpectrum (K ⊗[ℤ] O)) := IsArtinianRing.instFiniteMaximalSpectrum _
  obtain ⟨n₀, hn₀⟩ :=
    GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum (K ⊗[ℤ] O) N
  have hsc : ∀ (r : R) (m : M), algebraMap R K r • ((1 : K) ⊗ₜ[R] m) = (1 : K) ⊗ₜ[R] (r • m) := by
    intro r m
    rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have key : ∀ θ : K ⊗[R] M, ∃ s : R, algebraMap R K s ≠ 0 ∧
      ∃ m : M, algebraMap R K s • θ = (1 : K) ⊗ₜ[R] m := by
    intro θ
    induction θ using TensorProduct.induction_on with
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | tmul k m =>
      obtain ⟨a, s, hs, hk⟩ := hfrac k
      refine ⟨s, hs, a • m, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, hk, ← hsc, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
    | add x y hx hy =>
      obtain ⟨s, hs, m, hm⟩ := hx
      obtain ⟨t, ht, m', hm'⟩ := hy
      refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, t • m + s • m', ?_⟩
      rw [smul_add, map_mul, mul_comm, mul_smul, hm, mul_comm, mul_smul, hm', hsc, hsc,
        TensorProduct.tmul_add]
  obtain ⟨s, hs, m, hm⟩ := key (e.symm n₀)
  refine ⟨m, ?_⟩
  set k : K := algebraMap R K s with hk
  have hn : e ((1 : K) ⊗ₜ[R] m) = (k ⊗ₜ[ℤ] (1 : O)) • n₀ := by
    rw [← hm, map_smul, e.apply_symm_apply, TensorProduct.Algebra.smul_def, one_smul]
  have hu : IsUnit (k ⊗ₜ[ℤ] (1 : O)) := by
    refine ⟨⟨k ⊗ₜ[ℤ] (1 : O), k⁻¹ ⊗ₜ[ℤ] (1 : O), ?_, ?_⟩, rfl⟩ <;>
      simp [Algebra.TensorProduct.tmul_mul_tmul, hs, Algebra.TensorProduct.one_def]
  set n := e ((1 : K) ⊗ₜ[R] m) with hndef
  have hcomp : ∀ c : J →₀ K, e (Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m)) c)
      = (B.repr.symm c) • n := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, add_smul]
    | single i a =>
      rw [Finsupp.linearCombination_single, map_smul, he, B.repr_symm_single,
        Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
        TensorProduct.Algebra.smul_def]
  have hfun : ⇑(Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m)))
      = e.symm ∘ (fun x : K ⊗[ℤ] O => x • n) ∘ B.repr.symm := by
    funext c
    simp only [Function.comp_apply, ← hcomp c, e.symm_apply_apply]
  have hg : Function.Bijective (fun x : K ⊗[ℤ] O => x • n) := by
    have h1 : (fun x : K ⊗[ℤ] O => x • n)
        = (LinearMap.toSpanSingleton (K ⊗[ℤ] O) N n₀) ∘ (fun x => x * hu.unit) := by
      funext x
      simp [hn, mul_smul]
    rw [h1]
    exact hn₀.comp (Units.mulRight hu.unit).bijective
  rw [hfun]
  exact e.symm.bijective.comp (hg.comp B.repr.symm.bijective)
