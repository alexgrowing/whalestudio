import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeInt

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isReduced_of_isRegularRing (R : Type) [CommRing R] [IsRegularRing R] : IsReduced R :=
  isReduced_ofLocalizationMaximal R fun P _ => by
    haveI := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing (R := Localization.AtPrime P)
    infer_instance

theorem tensor_map_injective_of_field (A M K L : Type) [CommRing A] [CommRing M] [Algebra A M]
    [Field K] [Field L] [Algebra A K] [Algebra A L] (ι : K →ₐ[A] L) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id A M) ι) := by
  letI : Algebra K L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hcomp : (r.restrictScalars A) ∘ₗ ι.toLinearMap = LinearMap.id := by
    ext k
    exact LinearMap.congr_fun hr k
  intro x y hxy
  have h := congrArg (LinearMap.lTensor M (r.restrictScalars A)) hxy
  have key : ∀ z : M ⊗[A] K,
      LinearMap.lTensor M (r.restrictScalars A) (Algebra.TensorProduct.map (AlgHom.id A M) ι z) = z := by
    intro z
    have : (LinearMap.lTensor M (r.restrictScalars A)) ∘ₗ (LinearMap.lTensor M ι.toLinearMap) =
        LinearMap.id := by
      rw [← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_id]
    have e : Algebra.TensorProduct.map (AlgHom.id A M) ι z = LinearMap.lTensor M ι.toLinearMap z := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    rw [e]
    exact LinearMap.congr_fun this z
  rwa [key, key] at h

end GlobalTheory

namespace GlobalTheory

theorem formalFibre_isReduced_of_field :
    ∀ (A L : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [Field L] [Algebra A L],
      IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] L) := by
  intro A L _ _ _ _ _
  classical
  refine ⟨fun x hx => ?_⟩
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  set T : Subalgebra A L := Algebra.adjoin A ((S.image Prod.snd : Finset L) : Set L) with hT
  haveI : Algebra.FiniteType A T := (Subalgebra.fg_iff_finiteType T).mp (Subalgebra.fg_adjoin_finset _)
  let K := FractionRing T
  haveI : Algebra.EssFiniteType T K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType A K := Algebra.EssFiniteType.comp A T K
  have hinj : Function.Injective (IsScalarTower.toAlgHom T T L) := Subtype.val_injective
  let ι : K →ₐ[A] L := (IsFractionRing.liftAlgHom (K := K) hinj).restrictScalars A
  have hι : ∀ t : T, ι (algebraMap T K t) = t := fun t => by
    simp [ι, IsFractionRing.liftAlgHom_apply]
  have hmem : ∀ i ∈ S, i.2 ∈ T := fun i hi =>
    Algebra.subset_adjoin (by simpa using ⟨i.1, hi⟩)
  let y : AdicCompletion (maximalIdeal A) A ⊗[A] K :=
    ∑ i ∈ S.attach, i.1.1 ⊗ₜ[A] algebraMap T K ⟨i.1.2, hmem i.1 i.2⟩
  let Φ := Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (maximalIdeal A) A)) ι
  have hΦ : Φ y = ∑ i ∈ S, i.1 ⊗ₜ[A] i.2 := by
    simp only [y, map_sum, Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hι]
    exact Finset.sum_attach S (fun i => i.1 ⊗ₜ[A] i.2)
  haveI : IsRegularRing (AdicCompletion (maximalIdeal A) A ⊗[A] K) :=
    formalFibre_isRegularRing_of_essFiniteType_int A K
  haveI := isReduced_of_isRegularRing (AdicCompletion (maximalIdeal A) A ⊗[A] K)
  obtain ⟨n, hn⟩ := hx
  have hy : IsNilpotent y := ⟨n, tensor_map_injective_of_field A _ K L ι (by rw [map_pow, map_zero, hΦ, hn])⟩
  rw [← hΦ, IsReduced.eq_zero y hy, map_zero]

end GlobalTheory
