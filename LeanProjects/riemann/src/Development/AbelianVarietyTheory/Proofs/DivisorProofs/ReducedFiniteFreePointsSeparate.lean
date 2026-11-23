import Mathlib
set_option autoImplicit false
open scoped TensorProduct

namespace GlobalTheory

theorem finite_free_reduced_points_finite_and_separate
    (R K : Type) [CommRing R] [IsDomain R] [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    (r : R) (hr : r ≠ 0)
    (C : Type) [CommRing C] [Algebra R C] [Algebra (Localization.Away r) C]
    [IsScalarTower R (Localization.Away r) C]
    [Module.Finite (Localization.Away r) C] [Module.Free (Localization.Away r) C] (hC : IsReduced C) :
    Finite (C →ₐ[R] K) ∧ ∀ a : C, (∀ ψ : C →ₐ[R] K, ψ a = 0) → a = 0 := by
  have hu : IsUnit (algebraMap R K r) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr)
  letI : Algebra (Localization.Away r) K := (IsLocalization.Away.lift r hu).toAlgebra
  haveI : IsScalarTower R (Localization.Away r) K := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (IsLocalization.lift_eq _ x).symm)
  haveI : IsFractionRing (Localization.Away r) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) _ K

  have hS : ∀ ψ : C →ₐ[R] K, (ψ : C →+* K).comp (algebraMap (Localization.Away r) C) =
      algebraMap (Localization.Away r) K := by
    intro ψ
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    simp [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  let toS : (C →ₐ[R] K) → (C →ₐ[Localization.Away r] K) := fun ψ =>
    { (ψ : C →+* K) with commutes' := fun s => RingHom.congr_fun (hS ψ) s }
  have htoS : Function.Injective toS := by
    intro ψ₁ ψ₂ h
    ext c
    exact DFunLike.congr_fun h c
  refine ⟨Finite.of_injective toS htoS, ?_⟩
  intro a ha

  let ι : C →ₐ[Localization.Away r] K ⊗[Localization.Away r] C :=
    Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := C)
      (Algebra.linearMap (Localization.Away r) K) (IsFractionRing.injective (Localization.Away r) K)
    intro c d hcd
    apply (TensorProduct.lid (Localization.Away r) C).symm.injective
    apply h1
    simpa [ι] using hcd
  haveI : IsArtinianRing (K ⊗[Localization.Away r] C) :=
    IsArtinianRing.of_finite K (K ⊗[Localization.Away r] C)
  have hnil : ι a ∈ nilradical (K ⊗[Localization.Away r] C) := by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    haveI : Ideal.IsPrime J := hJ
    haveI : Ideal.IsMaximal J := IsArtinianRing.isMaximal_of_isPrime J
    letI : Field ((K ⊗[Localization.Away r] C) ⧸ J) := Ideal.Quotient.field J
    have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
      (K := (K ⊗[Localization.Away r] C) ⧸ J)
    let e := AlgEquiv.ofBijective (Algebra.ofId K ((K ⊗[Localization.Away r] C) ⧸ J)) hb
    let φ : K ⊗[Localization.Away r] C →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K J)
    let ψ : C →ₐ[R] K := (((φ.restrictScalars (Localization.Away r)).comp ι).restrictScalars R)
    have h0 : e.symm (Ideal.Quotient.mk J (ι a)) = 0 := ha ψ
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  obtain ⟨n, hn⟩ := mem_nilradical.mp hnil
  have han : a ^ n = 0 := hι (by rw [map_pow, hn, map_zero])
  exact (IsNilpotent.eq_zero ⟨n, han⟩)

end GlobalTheory
