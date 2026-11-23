import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeNefAboveSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def LocalizeRestrLen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (O : Type) [CommRing O] [Algebra S O]
    [IsLocalization.AtPrime O 𝔪] (Ω : Type) [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (pp' : Ideal (Kleiman.Poly O N)),
    (𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N) ≤ pp' →
    ∀ F : Kleiman.SubSystem S x Ω,
      Kleiman.restrLen pp' (F.baseChange O) =
        Kleiman.restrLen (pp'.comap (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N)) F

example (h : LocalizeRestrLen.Statement) :=
  h ℤ (Ideal.span {(2 : ℤ)}) LocalizeNefAbove.exO LocalizeNefAbove.exΩ 1 ![1, 1] _ le_rfl
    (Kleiman.twistSys ℤ ![1, 1] 1)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
