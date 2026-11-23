import Mathlib

open scoped PowerSeries TensorProduct

namespace GlobalTheory

open scoped PowerSeries TensorProduct in

theorem _root_.GlobalTheory.integralClosure_restrictScalars_of_isIntegral (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [Algebra.IsIntegral A A'] :
    (integralClosure A' B).restrictScalars A = integralClosure A B := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

section Contraction

variable {A : Type*} [CommRing A] (M : Submonoid A) {S : Type*} [CommRing S] [Algebra A S]
  [IsLocalization M S]

end Contraction

section PowerSeries

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

section Away

variable {ϖ : O} (hϖ : Irreducible ϖ) (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.Away (C ϖ : O⟦X⟧) S]

include hϖ

variable (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭 = Ideal.span {algebraMap O⟦X⟧ S X})
  (V : Type*) [CommRing V] [Algebra S V] [IsLocalization.AtPrime V 𝔭]

include h𝔭

end Away

end PowerSeries

universe u

end GlobalTheory
