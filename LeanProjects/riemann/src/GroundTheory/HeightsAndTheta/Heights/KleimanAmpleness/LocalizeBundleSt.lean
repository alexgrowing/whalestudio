import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseChangeObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def LocalizeBundle.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsPrime] (O : Type) [CommRing O] [Algebra S O]
    [IsLocalization.AtPrime O 𝔪] (Ω : Type) [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : Kleiman.LineBundle S x),
    ∃ M' : Kleiman.LineBundle O x, M'.toSubSystem = M.toSubSystem.baseChange O

instance LocalizeBundle.hyps : (Ideal.span {(2 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two

abbrev LocalizeBundle.exO : Type := Localization.AtPrime (Ideal.span {(2 : ℤ)})

abbrev LocalizeBundle.exΩ : Type := FractionRing LocalizeBundle.exO

instance LocalizeBundle.exTower : @IsScalarTower ℤ LocalizeBundle.exO LocalizeBundle.exΩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)

example (h : LocalizeBundle.Statement) :=
  h ℤ (Ideal.span {(2 : ℤ)}) LocalizeBundle.exO LocalizeBundle.exΩ 1 ![1, 1]
    (Kleiman.twistBundle ℤ ![1, 1] 1)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
