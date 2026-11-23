import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem normal_atPrime_tensor_of_chart_localization : ∀ (A B D R : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing R] [Algebra A B] [Algebra A D] [Algebra A R] (ι : D →ₐ[A] B), Function.Injective ι → (∀ b, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a) → ∀ (Q : Ideal (B ⊗[A] R)) [Q.IsPrime] (q : Ideal (D ⊗[A] R)) [q.IsPrime], Q.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q → IsDomain (Localization.AtPrime q) → IsIntegrallyClosed (Localization.AtPrime q) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro A B D R _ _ _ _ _ _ _ ι hinj hsurj Q _ q _ hle hdom hic
  letI : Algebra D B := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A D B := .of_algebraMap_eq fun a ↦ (ι.commutes a).symm
  let M : Submonoid D := (IsUnit.submonoid B).comap ι.toRingHom
  haveI : IsLocalization M B :=
    { map_units := fun y ↦ y.2
      surj := fun b ↦ by
        obtain ⟨a, s, hs, h⟩ := hsurj b
        exact ⟨(a, ⟨s, hs⟩), by rw [mul_comm]; exact h⟩
      exists_of_eq := fun {x y} h ↦ ⟨1, by rw [hinj h]⟩ }
  let φ := Algebra.TensorProduct.map ι (AlgHom.id A R)
  letI : Algebra (D ⊗[A] R) (B ⊗[A] R) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower D (D ⊗[A] R) (B ⊗[A] R) := .of_algebraMap_eq fun x ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply, φ]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (D ⊗[A] R) M) (B ⊗[A] R) :=
    IsLocalization.tensorProduct_tensorProduct A R M B (by
      ext x; simp [RingHom.algebraMap_toAlgebra, φ])
  set QD := Q.comap (algebraMap (D ⊗[A] R) (B ⊗[A] R)) with hQD
  haveI : QD.IsPrime := Ideal.comap_isPrime _ _
  haveI hL : IsLocalization QD.primeCompl (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (D ⊗[A] R) M) (Localization.AtPrime Q) Q
  have hle' : q.primeCompl ≤ QD.primeCompl := fun x hx hx' ↦ hx (hle hx')
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ q.primeCompl QD.primeCompl hle'
  haveI : IsScalarTower (D ⊗[A] R) (Localization.AtPrime q) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ q.primeCompl QD.primeCompl hle'
  haveI : IsLocalization (QD.primeCompl.map (algebraMap (D ⊗[A] R) (Localization.AtPrime q)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ q.primeCompl QD.primeCompl hle'
  have hN : QD.primeCompl.map (algebraMap (D ⊗[A] R) (Localization.AtPrime q)) ≤
      nonZeroDivisors (Localization.AtPrime q) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have hu : IsUnit (algebraMap (D ⊗[A] R) (Localization.AtPrime Q) c) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨c, hc⟩ : QD.primeCompl)
    rw [IsScalarTower.algebraMap_apply (D ⊗[A] R) (Localization.AtPrime q)
      (Localization.AtPrime Q), h0, map_zero] at hu
    exact not_isUnit_zero hu
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors _ hN,
    isIntegrallyClosed_of_isLocalization _ _ hN⟩

end GlobalTheory
