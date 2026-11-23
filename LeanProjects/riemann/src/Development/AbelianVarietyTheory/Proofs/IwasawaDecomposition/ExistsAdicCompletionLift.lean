import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
open IsLocalRing

namespace GlobalTheory

theorem exists_maximalIdeal_adicCompletion_lift :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R),
      IsAdicComplete (maximalIdeal R) R → (maximalIdeal A).map φ = maximalIdeal R →
      ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R,
        ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  intro A R _ _ _ _ φ hc hm
  haveI : IsAdicComplete ((maximalIdeal A).map φ) R := hm ▸ hc
  exact exists_adicCompletion_ringHom_extend (maximalIdeal A) φ

end GlobalTheory
