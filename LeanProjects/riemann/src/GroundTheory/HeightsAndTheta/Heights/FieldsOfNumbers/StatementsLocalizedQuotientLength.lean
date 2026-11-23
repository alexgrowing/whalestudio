import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u v

def LocalizedQuotientLength.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (P W : Ideal S) [W.IsPrime] (x : S) (R : Type v) [CommRing R]
    [Algebra (S ⧸ P) R], IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) R →
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (S ⧸ (P ⊔ Ideal.span {x}))) =
        Module.length R (R ⧸ Ideal.span {algebraMap (S ⧸ P) R (Ideal.Quotient.mk P x)})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
