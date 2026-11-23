import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsNefGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def FibreRestrKer.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDedekindDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (L : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ qq : Ideal (Poly S N), qq.IsPrime → (∀ s : S, (C s : Poly S N) ∈ qq → s = 0) →
    ∀ e : ℕ, IsSubvar x (qq.map (MvPolynomial.map (algebraMap S F))) e →
    ∀ᶠ c : ℕ in atTop,
      ((L.toSubSystem.twist (twistSys S x (c : ℤ))).twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).secs =
        ((L.toSubSystem.twist (twistSys S x (c : ℤ))).twist (idealSys x qq)).secs ⊔
          𝔪 • (L.toSubSystem.twist (twistSys S x (c : ℤ))).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
