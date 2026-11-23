import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseChangeObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def LocalizeNefAbove.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (O : Type) [CommRing O] [Algebra S O]
    [IsLocalization.AtPrime O 𝔪] (Ω : Type) [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : Kleiman.SubSystem S x Ω),
    Kleiman.NefAbove M (𝔪.map (C : S →+* Kleiman.Poly S N)) →
    Kleiman.NefAbove (M.baseChange O) ((𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N))

instance LocalizeNefAbove.hyps₁ : (Ideal.span {(2 : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two).isMaximal (by simp)

abbrev LocalizeNefAbove.exO : Type := Localization.AtPrime (Ideal.span {(2 : ℤ)})

abbrev LocalizeNefAbove.exΩ : Type := FractionRing LocalizeNefAbove.exO

instance LocalizeNefAbove.exTower : @IsScalarTower ℤ LocalizeNefAbove.exO LocalizeNefAbove.exΩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)

theorem LocalizeNefAbove.hyps₂ :
    Kleiman.NefAbove (Kleiman.twistSys ℤ (![1, 1] : Fin 2 → LocalizeNefAbove.exΩ) 0)
      ((Ideal.span {(2 : ℤ)}).map (C : ℤ →+* Kleiman.Poly ℤ 1)) :=
  fun pp _ _ => by rw [Kleiman.interNum_twistSys_zero]

example (h : LocalizeNefAbove.Statement) :=
  h ℤ (Ideal.span {(2 : ℤ)}) LocalizeNefAbove.exO LocalizeNefAbove.exΩ 1 ![1, 1] _ LocalizeNefAbove.hyps₂

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
