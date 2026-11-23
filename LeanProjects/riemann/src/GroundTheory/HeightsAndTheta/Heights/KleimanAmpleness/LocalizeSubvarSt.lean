import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseChangeObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def LocalizeSubvar.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (O : Type) [CommRing O] [Algebra S O]
    [IsLocalization.AtPrime O 𝔪] (Ω : Type) [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (pp' : Ideal (Kleiman.Poly O N)) (e : ℕ),
    (𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N) ≤ pp' → Kleiman.IsSubvar x pp' e →
    Kleiman.IsSubvar x
      (pp'.comap (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N)) e

instance LocalizeSubvar.exLoc (k : Type) [Field k] : IsLocalization.AtPrime k (⊥ : Ideal k) :=
  IsLocalization.of_le_isUnit fun a ha =>
    (IsUnit.mem_submonoid_iff a).mpr (isUnit_iff_ne_zero.mpr fun h => ha (h ▸ Ideal.zero_mem _))

theorem LocalizeSubvar.hyps (k : Type) [Field k] (N : ℕ) :
    ((⊥ : Ideal k).map (algebraMap k k)).map (C : k →+* Kleiman.Poly k N) ≤
        Kleiman.primeOf (S := k) (Kleiman.genericPt k N) ∧
      Kleiman.IsSubvar (Kleiman.genericPt k N) (Kleiman.primeOf (S := k) (Kleiman.genericPt k N)) N :=
  ⟨by rw [Ideal.map_bot, Ideal.map_bot]; exact bot_le, Kleiman.isSubvar_genericPt k N⟩

example (k : Type) [Field k] (h : LocalizeSubvar.Statement) :=
  h k ⊥ k (FractionRing (Kleiman.Poly k 1)) 1 (Kleiman.genericPt k 1) _ 1 (LocalizeSubvar.hyps k 1).1
    (LocalizeSubvar.hyps k 1).2

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
