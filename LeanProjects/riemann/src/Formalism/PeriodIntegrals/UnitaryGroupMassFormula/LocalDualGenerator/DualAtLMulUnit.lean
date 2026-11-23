import Mathlib
import Formalism.PeriodIntegrals.LocDualGen

noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocDualGen.Part2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

theorem alg_mem_O (r : 𝒪[A.Fp]) : algebraMap A.Fp A.Ep (r : A.Fp) ∈ A.O := by
  rw [A.O_def]
  have : algebraMap A.Fp A.Ep (r : A.Fp) = algebraMap 𝒪[A.Fp] A.Ep r := rfl
  rw [this]
  exact isIntegral_algebraMap

theorem dualAtL_mul_unit (δ : A.Fp) (u : 𝒪[A.Fp]) (hu : IsUnit u) (h : DualAtL A δ) :
    DualAtL A (δ * (u : A.Fp)) := by
  intro x
  rw [← h x]
  obtain ⟨v, rfl⟩ := hu
  have hv : ((v : 𝒪[A.Fp]) : A.Fp) * ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  set a := algebraMap A.Fp A.Ep ((v : 𝒪[A.Fp]) : A.Fp)
  set b := algebraMap A.Fp A.Ep ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp)
  have hab : a * b = 1 := by rw [← map_mul, hv, map_one]
  have hinv : (((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) :=
    inv_eq_of_mul_eq_one_right hv
  have key : algebraMap A.Fp A.Ep (δ * ((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = algebraMap A.Fp A.Ep δ⁻¹ * b := by
    rw [mul_inv, map_mul, hinv]
  constructor
  · intro H y hy
    have := H (y * a) (A.O.mul_mem hy (alg_mem_O A _))
    rwa [key, show x * (y * a) * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * y * algebraMap A.Fp A.Ep δ⁻¹ * (a * b) by ring,
      hab, mul_one] at this
  · intro H y hy
    have := H (y * b) (A.O.mul_mem hy (alg_mem_O A _))
    rwa [key, show x * y * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * (y * b) * algebraMap A.Fp A.Ep δ⁻¹ by ring]

end PI.LocDualGen.Part2
