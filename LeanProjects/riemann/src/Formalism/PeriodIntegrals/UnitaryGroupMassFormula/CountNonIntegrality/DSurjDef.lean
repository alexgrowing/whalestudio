import Mathlib

noncomputable section

namespace PI.CntNotIntW

open scoped TensorProduct

def piMap (K : Type) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [Algebra ℚ_[ℓ] Fp] (ι : K →+* Fp) :
    ℚ_[ℓ] ⊗[ℚ] K →ₐ[ℚ_[ℓ]] Fp :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[ℓ] Fp) ι.toRatAlgHom (fun _ _ => Commute.all _ _)

def PiSurj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [ValuativeRel Fp]
    [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp],
    Continuous (algebraMap ℚ_[ℓ] Fp) → FiniteDimensional ℚ_[ℓ] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
      Function.Surjective (piMap K ℓ Fp ι)

theorem piMap_one_tmul (K : Type) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [Algebra ℚ_[ℓ] Fp]
    (ι : K →+* Fp) (y : K) : piMap K ℓ Fp ι (1 ⊗ₜ y) = ι y := by
  simp [piMap]

end PI.CntNotIntW
