import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepEx :
    RepEx := by
  intro E _ _ n
  classical
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let bQ := Pi.basis (fun _ : Fin n => NumberField.integralBasis E)
  let b1 := Algebra.TensorProduct.basis ℚ bZ
  refine ⟨b1.equiv bQ (Equiv.refl _), ?_⟩
  let f1 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    ((b1.equiv bQ (Equiv.refl _)).toLinearMap.restrictScalars ℤ) ∘ₗ
      TensorProduct.mk ℤ ℚ (Fin n → 𝓞 E) 1
  let f2 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    LinearMap.pi (fun i => (algebraMap (𝓞 E) E).toIntAlgHom.toLinearMap ∘ₗ LinearMap.proj i)
  have hf : f1 = f2 := by
    refine bZ.ext fun k => ?_
    have hk : f1 (bZ k) = b1.equiv bQ (Equiv.refl _) (b1 k) := by
      rw [Algebra.TensorProduct.basis_apply]
      rfl
    rw [hk, Module.Basis.equiv_apply]
    obtain ⟨i, j⟩ := k
    funext l
    simp [bQ, bZ, f2, Pi.basis_apply, Pi.single_apply, NumberField.integralBasis_apply]
    split_ifs <;> simp
    rfl
  intro v i
  exact congr_fun (LinearMap.congr_fun hf v) i
