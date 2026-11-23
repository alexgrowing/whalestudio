import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalFlat
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsLocalizedQuotientLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u

set_option maxHeartbeats 400000 in

theorem ConeLocalLength.proof (h₁ : LocalizedQuotientLength.Statement.{u, u})
    (h₂ : ConeLocalFlat.Statement.{u}) : ConeLocalLength.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW c a h _ _ hhW α hα
  have := hP.isPrime
  have := hW.isPrime
  obtain ⟨_, _, _, hmax⟩ := h₂ F K ι P hP W hW hPW
  have : IsLocalHom (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) :=
    ((local_hom_TFAE _).out 2 0).mp hmax.le
  have hu : IsUnit (algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h)) :=
    IsLocalization.map_units (coneLocal P W hPW)
      (⟨_, ⟨h, hhW, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have hne : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P h) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h' => hhW (hPW h')
  have ha : algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P a) =
      algebraMap (degZeroLoc P {W}) (coneLocal P W hPW) α *
        algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, degZeroLoc.algebraMap_cone_coe, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, hα, div_mul_cancel₀ _ hne]
  have hspan : Ideal.span {algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P a)} =
      (Ideal.span {α}).map (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) := by
    rw [Ideal.map_span, Set.image_singleton, ha, Ideal.span_singleton_mul_right_unit hu]

  have key : ∀ (A R : Type u) [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
      [Algebra A R] [IsLocalHom (algebraMap A R)] [Module.Flat A R],
      (maximalIdeal A).map (algebraMap A R) = maximalIdeal R → ∀ x : A,
        Module.length R (R ⧸ (Ideal.span {x}).map (algebraMap A R)) = Ring.ord A x := by
    intro A R _ _ _ _ _ _ _ hm x
    have hs : Module.length R (R ⧸ maximalIdeal R) = 1 := Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)
    rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (Ideal.span {x})).toLinearEquiv.length_eq,
      IsLocalRing.length_baseChange, hm, hs, mul_one]
    rfl
  unfold multAt
  rw [h₁ _ P W a (coneLocal P W hPW) inferInstance, hspan]
  exact key (degZeroLoc P {W}) (coneLocal P W hPW) hmax α

end

end GroundTheory.Heights₂.Heights.FieldNumbers
