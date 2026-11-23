import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial IsLocalRing

theorem localization_span_singleton_dvr {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a : A) (ha : a ≠ 0) [hP : (Ideal.span {a}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {a})) ∧
      Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {a})) a) := by
  set L := Localization.AtPrime (Ideal.span {a})
  have : IsDomain L :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))
  have : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (Ideal.span {a}).primeCompl L inferInstance
  have hmax : maximalIdeal L = Ideal.span {algebraMap A L a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {a}) L, Ideal.map_span,
      Set.image_singleton]
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))
  have hne : algebraMap A L a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hnf : ¬ IsField L := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hne
  have hdvr : IsDiscreteValuationRing L :=
    ((IsDiscreteValuationRing.TFAE L hnf).out 4 0).mp (⟨⟨_, hmax⟩⟩ : (maximalIdeal L).IsPrincipal)
  exact ⟨hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax⟩

theorem DiagonalLocalDVR.proof (h0 : DiagonalQuotient.Statement) : DiagonalLocalDVR.Statement := by
  intro R _ _ _
  have hd : (diagonalIdeal R).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (h0 R).2.2.1 inferInstance
  have hm : (mixedDiagonalIdeal R).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (h0 R).2.2.2.2.2 inferInstance
  have h1 : (X 0 - X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![(1 : R), 0]) h
    simp at this
  have h2 : (1 - X 0 * X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![(0 : R), 0]) h
    simp at this
  exact ⟨⟨hd, @localization_span_singleton_dvr _ _ _ _ _ h1 hd⟩,
    ⟨hm, @localization_span_singleton_dvr _ _ _ _ _ h2 hm⟩⟩

end GroundTheory.Heights₂.Heights.FlagBundles
