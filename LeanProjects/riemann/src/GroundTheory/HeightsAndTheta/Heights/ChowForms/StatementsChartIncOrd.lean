import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartIncOrd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
    [(W.map (chartX I t e)).IsPrime]
    [(W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime]
    (x : MvPolynomial (Fin n) F),
    Ring.ord (Localization.AtPrime (W.map (chartX I t e)))
        (algebraMap (ChartInc I t e) _ (chartX I t e x)) =
      Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
        (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) x))

section Inhabitants

theorem isPrime_map_of_sup_ker {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (K : Ideal R) (h : (K ⊔ RingHom.ker f).IsPrime) : (K.map f).IsPrime := by
  have e : K.map f = (K ⊔ RingHom.ker f).map f := by
    rw [Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker f).mpr le_rfl, sup_bot_eq]
  rw [e]
  exact Ideal.map_isPrime_of_surjective hf le_sup_right

def evalPtLine : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ℚ := aeval ![0, 1]

def evalIncLine : MvPolynomial (Fin 2 ⊕ Fin 1 × Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 1 × Fin 2) ℚ :=
  aeval (Sum.elim ![0, 1] fun ij => if ij.2 = 0 then X ij else 0)

end Inhabitants

end

end GroundTheory.Heights₂.Heights
