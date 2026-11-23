import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdDeterminesPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

instance isIntegral_curveNormalisation (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
  inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
    ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))

theorem ringKrullDim_curveNormalisation_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    ringKrullDim (curveNormalisation I q) ≤ ringKrullDim (curveLocalRing I q) :=
  Order.krullDim_le_of_strictMono
    (fun Q ↦ ⟨Q.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)), inferInstance⟩)
    fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap (R := curveLocalRing I q) h

theorem exists_ord_eq_ord_polynomial (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (a : curveLocalRing I q) : ∃ f : MvPolynomial (Fin n) ℂ, ∀ P : MaximalSpectrum (curveNormalisation I q),
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨⟨f, h⟩, hfh⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl y
  refine ⟨f, fun P ↦ ?_⟩
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (h : MvPolynomial (Fin n) ℂ)) :=
    isUnit_algebraMap_curveLocalRing I q h fun H ↦ h.2 (RingHom.mem_ker.2 H)
  let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
  have hπ : ∀ g : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g =
      π (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) g) := fun _ ↦ rfl
  have hy' : π y = a := hy
  have hfh' : IsLocalization.mk' (Localization.AtPrime (RingHom.ker (eval q))) f h = y := hfh
  have heq : a *
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (h : MvPolynomial (Fin n) ℂ) =
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
    rw [← hy', ← hfh', hπ, hπ, ← map_mul, IsLocalization.mk'_spec]
  rw [← heq, map_mul, map_mul, Ring.ord_mul_of_isUnit_right ((hu.map _).map _)]

theorem OrdDeterminesPlace.proof (hfin : CurveNormalisationFinite.Statement) : OrdDeterminesPlace.Statement := by
  intro n I q hrad hdim P P' hord
  have : Module.Finite (curveLocalRing I q) (curveNormalisation I q) := hfin n I q hrad
  have : IsNoetherianRing (curveNormalisation I q) := IsNoetherianRing.of_finite (curveLocalRing I q) _

  have hdimP : ∀ Q : MaximalSpectrum (curveNormalisation I q), Ring.KrullDimLE 1 (Localization.AtPrime Q.asIdeal) := by
    intro Q
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height Q.asIdeal]
    calc (Q.asIdeal.height : WithBot ℕ∞) ≤ ringKrullDim (curveNormalisation I q) :=
          Ideal.height_le_ringKrullDim_of_ne_top Q.isMaximal.ne_top
      _ ≤ ringKrullDim (curveLocalRing I q) := ringKrullDim_curveNormalisation_le I q
      _ = 1 := by rw [hdim]

  have hO : ∀ a : curveLocalRing I q,
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) := by
    intro a
    obtain ⟨f, hf⟩ := exists_ord_eq_ord_polynomial I q a
    rw [hf P, hf P', hord f]
  by_contra hne
  obtain ⟨x, hxP, hxP'⟩ : ∃ x, x ∈ P.asIdeal ∧ x ∉ P'.asIdeal := by
    by_contra! H
    exact hne (MaximalSpectrum.ext (P.isMaximal.eq_of_le P'.isMaximal.ne_top H))

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (curveLocalRing I q))
    (show ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))) from x).1
  have hax : algebraMap (curveLocalRing I q) (curveNormalisation I q) a =
      algebraMap (curveLocalRing I q) (curveNormalisation I q) s * x := by
    apply Subtype.ext
    change algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) a =
      algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) s * (show ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))) from x).1
    rw [← hs, IsLocalization.mk'_spec']

  have hsN : algebraMap (curveLocalRing I q) (curveNormalisation I q) s ∈ nonZeroDivisors (curveNormalisation I q) := by
    have hu : IsUnit (algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) s) :=
      IsLocalization.map_units _ s
    exact mem_nonZeroDivisors_of_injective (f := (integralClosure (curveLocalRing I q)
      (FractionRing (curveLocalRing I q))).val) Subtype.val_injective hu.mem_nonZeroDivisors
  have hsP : ∀ Q : MaximalSpectrum (curveNormalisation I q),
      algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s) ∈
        nonZeroDivisors (Localization.AtPrime Q.asIdeal) := fun Q ↦
    IsLocalization.nonZeroDivisors_le_comap Q.asIdeal.primeCompl _ hsN

  have h' : Ring.ord (Localization.AtPrime P'.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
      Ring.ord (Localization.AtPrime P'.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) := by
    rw [hax, map_mul, Ring.ord_mul_of_isUnit_right]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P'.asIdeal x).2 hxP'

  have hP : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
      Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) +
      Ring.ord (Localization.AtPrime P.asIdeal)
        (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) := by
    rw [hax, map_mul, Ring.ord_mul' _ (hsP P)]
  have hfin' : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) ≠ ⊤ := by
    have := hdimP P
    exact Ring.ord_ne_top (hsP P)
  rw [hO a, h', ← hO s] at hP
  have hx0 : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) = 0 := by
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hfin'
    rw [← hk] at hP
    generalize Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) = y at hP ⊢
    induction y using ENat.recTopCoe with
    | top => simp at hP
    | coe m => norm_cast at hP ⊢; omega

  rw [Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at hx0
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P.asIdeal x).1 hx0 hxP

end

end GroundTheory.Heights₂.Heights
