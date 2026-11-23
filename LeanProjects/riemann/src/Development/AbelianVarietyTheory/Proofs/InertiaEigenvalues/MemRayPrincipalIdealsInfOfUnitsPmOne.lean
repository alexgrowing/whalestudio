import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.RayPrincipalInf

open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals

variable {K : Type} [Field K] [NumberField K]

theorem not_mem_of_coprime {𝔞 𝔭 : Ideal (𝓞 K)} {b : 𝓞 K} (h : IsCoprime (Ideal.span {b}) 𝔞) (hle : 𝔞 ≤ 𝔭)
    (hp : 𝔭 ≠ ⊤) : b ∉ 𝔭 := by
  intro hb
  apply hp
  rw [Ideal.isCoprime_iff_sup_eq] at h
  rw [eq_top_iff, ← h]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hb) hle

end GlobalTheory.RayPrincipalInf
