import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private theorem UpperTheory.tensor_rat_injective_of_free {L : Type} [AddCommGroup L] [Module.Free ℤ L] :
    Function.Injective (TensorProduct.mk ℤ ℚ L (1 : ℚ)) := by
  have hf : Function.Injective (Algebra.linearMap ℤ ℚ) :=
    fun a b h => by simpa using h
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := L) (Algebra.linearMap ℤ ℚ) hf
  intro x y hxy
  apply (TensorProduct.lid ℤ L).symm.injective
  apply h
  simpa [LinearMap.rTensor_tmul] using hxy

theorem UpperTheory.finite_free_of_bounded_denominators_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), (∃ d : ℕ, 0 < d ∧ ∀ w ∈ X.lat, ∃ a : D.La, d • w = (1 : ℚ) ⊗ₜ[ℤ] a) → Module.Finite ℤ X.lat ∧ Module.Free ℤ X.lat := by
  intro p _ D X ⟨d, hd, h⟩
  haveI := D.freeLa
  haveI := D.finLa
  let ι : D.La →ₗ[ℤ] VQ D := TensorProduct.mk ℤ ℚ D.La (1 : ℚ)
  have hι : Function.Injective ι := UpperTheory.tensor_rat_injective_of_free
  let g : X.lat →ₗ[ℤ] VQ D := (d : ℤ) • (X.lat.toIntSubmodule.subtype)
  have hg : Function.Injective g := by
    intro u v huv
    have h1 : (d : ℤ) • (u : VQ D) = (d : ℤ) • (v : VQ D) := huv
    have hq : ((d : ℚ)) • (u : VQ D) = (d : ℚ) • (v : VQ D) := by
      simpa [Nat.cast_smul_eq_nsmul] using h1
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    exact Subtype.ext (smul_right_injective _ hd0 hq)
  have hr : ∀ w, g w ∈ LinearMap.range ι := by
    intro w
    obtain ⟨a, ha⟩ := h w w.2
    refine ⟨a, ?_⟩
    change (1 : ℚ) ⊗ₜ[ℤ] a = (d : ℤ) • (w : VQ D)
    rw [← ha]
    exact (natCast_zsmul (w : VQ D) d).symm
  let f : X.lat →ₗ[ℤ] D.La :=
    (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ g.codRestrict (LinearMap.range ι) hr
  have hf : Function.Injective f := by
    intro u v huv
    apply hg
    have := (LinearEquiv.ofInjective ι hι).symm.injective huv
    exact congrArg Subtype.val this
  refine ⟨Module.Finite.of_injective f hf, ?_⟩
  exact Module.Free.of_equiv (LinearEquiv.ofInjective f hf).symm
