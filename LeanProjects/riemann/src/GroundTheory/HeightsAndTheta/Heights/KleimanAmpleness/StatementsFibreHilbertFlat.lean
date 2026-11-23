import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsNefGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def FibreHilbertFlat.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDedekindDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ qq : Ideal (Poly S N), qq.IsPrime → (∀ s : S, (C s : Poly S N) ∈ qq → s = 0) →
    IsSubvar x (qq.map (MvPolynomial.map (algebraMap S F))) 1 →
    ∀ᶠ c : ℕ in atTop,
      interSum (qq.map (MvPolynomial.map (algebraMap S F))) ![M.toSubSystem.extend F] c =
        interSum (qq ⊔ 𝔪.map (C : S →+* Poly S N)) ![M.toSubSystem] c

end

end GroundTheory.Heights₂.Heights.Kleiman
