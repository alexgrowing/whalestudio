import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationQuotientLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StExtensionQuotientLength
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem length_quotient_sup_span {L : Type} [CommRing L] (J : Ideal L) (g : L) :
    Module.length L (L ⧸ (J ⊔ Ideal.span {g})) =
      Module.length (L ⧸ J) ((L ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J g}) := by
  have hK : (Ideal.span {g}).map (Ideal.Quotient.mkₐ L J) = Ideal.span {Ideal.Quotient.mk J g} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← (DoubleQuot.quotQuotEquivQuotSupₐ L J (Ideal.span {g})).toLinearEquiv.length_eq, hK]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem length_localization_eq_length_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    Module.length (Localization.AtPrime (RingHom.ker (eval q)))
        (Localization.AtPrime (RingHom.ker (eval q)) ⧸ (I ⊔ Ideal.span {f}).map
          (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))) =
      Module.length (curveLocalRing I q)
        (curveLocalRing I q ⧸ Ideal.span {algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f}) := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact length_quotient_sup_span _ _

theorem length_quotient_ne_top {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hdim : ringKrullDim O = 1) {x : O} (hx : x ∈ nonZeroDivisors O) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by
  by_cases hm : x ∈ IsLocalRing.maximalIdeal O
  · have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hx hm
    rw [hdim] at h
    have h0 : ringKrullDim (O ⧸ Ideal.span {x}) ≤ (0 : ℕ) := by
      generalize ringKrullDim (O ⧸ Ideal.span {x}) = d at h ⊢
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe k =>
        have h' : k + 1 = 1 := by exact_mod_cast h
        induction k using ENat.recTopCoe with
        | top => simp at h'
        | coe m =>
          have hm : m + 1 = 1 := by exact_mod_cast h'
          have : m = 0 := by omega
          subst this
          simp
    have : Ring.KrullDimLE 0 (O ⧸ Ideal.span {x}) := Ring.krullDimLE_iff.2 h0
    have := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := O ⧸ Ideal.span {x})
    rw [Module.length_eq_of_surjective (R := O ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective]
    exact Module.length_ne_top
  · have hu : IsUnit x := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hm
    rw [Ideal.span_singleton_eq_top.2 hu,
      Module.length_eq_zero_iff.2 (Ideal.Quotient.subsingleton_iff.2 rfl)]
    exact ENat.zero_ne_top

theorem CurveNormalisationLength.proof (hFin : CurveNormalisationFinite.Statement)
    (hQ : CurveNormalisationQuotientLength.Statement) (hE : ExtensionQuotientLength.Statement) :
    CurveNormalisationLength.Statement := by
  intro n I q f hrad hdim hf
  set O := curveLocalRing I q
  set f' := algebraMap (MvPolynomial (Fin n) ℂ) O f
  have : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing O := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Module.Finite O (curveNormalisation I q) := hFin n I q hrad
  have hfin := length_quotient_ne_top hdim hf

  have hnzd : algebraMap O (curveNormalisation I q) f' ∈ nonZeroDivisors (curveNormalisation I q) := by
    let ι : curveNormalisation I q →+* FractionRing O :=
      (integralClosure O (FractionRing O)).val.toRingHom
    refine mem_nonZeroDivisors_of_injective (f := ι) Subtype.val_injective ?_
    exact (IsLocalization.map_units (FractionRing O) (⟨f', hf⟩ : nonZeroDivisors O)).mem_nonZeroDivisors
  have hEq := hE O (curveNormalisation I q) f' (algebraMap_curveNormalisation_injective I q) hnzd
    (hQ n I q hrad hdim)
  rw [localMult, dif_pos (isPrime_ker_eval q), length_localization_eq_length_curveLocalRing,
    ENat.natCast_toNat hfin, hEq]
  exact GroundTheory.Heights₂.Heights.Vertical.LengthDecomp.proof O (curveNormalisation I q) _ (hEq ▸ hfin)

end

end GroundTheory.Heights₂.Heights
