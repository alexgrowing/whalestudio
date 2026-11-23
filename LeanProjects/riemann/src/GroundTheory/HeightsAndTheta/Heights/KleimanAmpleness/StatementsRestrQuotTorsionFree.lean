import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsNefGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def RestrQuotTorsionFree.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDedekindDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (L : LineBundle S x),
    ∀ qq : Ideal (Poly S N), qq.IsPrime → (∀ s : S, (C s : Poly S N) ∈ qq → s = 0) →
    ∀ e : ℕ, IsSubvar x (qq.map (MvPolynomial.map (algebraMap S F))) e →
    Module.IsTorsionFree S (L.secs ⧸ ((L.twist (idealSys x qq)).secs).comap L.secs.subtype)

end

end GroundTheory.Heights₂.Heights.Kleiman
