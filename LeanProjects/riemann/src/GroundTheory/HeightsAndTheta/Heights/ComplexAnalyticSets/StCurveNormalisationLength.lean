import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

instance isPrime_ker_eval (q : Fin n → ℂ) : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _

def curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : CommRing (curveLocalRing I q) :=
  inferInstanceAs (CommRing (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : IsNoetherianRing (curveLocalRing I q) :=
  inferInstanceAs (IsNoetherianRing (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))

def curveNormalisation (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q)))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : CommRing (curveNormalisation I q) :=
  inferInstanceAs (CommRing ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra (curveLocalRing I q) (curveNormalisation I q) :=
  inferInstanceAs
    (Algebra (curveLocalRing I q) ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))

theorem isUnit_algebraMap_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) := by
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) f) :=
    IsLocalization.map_units _ (⟨f, fun h ↦ hf (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl)
  exact hu.map (Ideal.Quotient.mk _)

theorem curveLocalRing_subsingleton (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (hq : q ∉ zeroSet I) : Subsingleton (curveLocalRing I q) := by
  simp only [zeroSet, Set.mem_ofPred_eq, not_forall] at hq
  obtain ⟨g, hg, hgq⟩ := hq
  unfold curveLocalRing
  rw [Ideal.Quotient.subsingleton_iff]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
    (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))

theorem algebraMap_curveNormalisation_injective (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Function.Injective (algebraMap (curveLocalRing I q) (curveNormalisation I q)) := by
  intro a b h
  exact IsLocalization.injective (FractionRing (curveLocalRing I q)) le_rfl (congrArg Subtype.val h)

theorem height_ker_eval_line : (RingHom.ker (eval (0 : Fin 1 → ℂ))).height = 1 := by
  apply le_antisymm
  · have h := Ideal.height_le_ringKrullDim_of_ne_top
      (I := RingHom.ker (eval (0 : Fin 1 → ℂ))) (RingHom.ker_ne_top _)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact_mod_cast h
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    have hX : (X 0 : MvPolynomial (Fin 1) ℂ) ∈ RingHom.ker (eval (0 : Fin 1 → ℂ)) := by simp
    rw [h, Ideal.mem_bot] at hX
    exact X_ne_zero _ hX

def curveLocalRingLineEquiv :
    curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0 ≃+*
      Localization.AtPrime (RingHom.ker (eval (0 : Fin 1 → ℂ))) :=
  (Ideal.quotEquivOfEq (Ideal.map_bot)).trans (RingEquiv.quotientBot _)

theorem ringKrullDim_curveLocalRing_line :
    ringKrullDim (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) = 1 := by
  rw [ringKrullDim_eq_of_ringEquiv curveLocalRingLineEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (RingHom.ker (eval (0 : Fin 1 → ℂ))),
    height_ker_eval_line]
  rfl

def CurveNormalisationLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q) →
      (localMult (I ⊔ Ideal.span {f}) (RingHom.ker (eval q)) : ℕ∞) =
        ∑ᶠ P : MaximalSpectrum (curveNormalisation I q),
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
                (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) *
            Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ P.asIdeal)

theorem CurveNormalisationLength.hypotheses_inhabited :
    IsRadicalAt (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0 ∧
      ringKrullDim (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) = 1 ∧
      algebraMap (MvPolynomial (Fin 1) ℂ) (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) (X 0) ∈
        nonZeroDivisors (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) := by
  refine ⟨isRadicalAt_of_isRadical Ideal.isPrime_bot.isRadical 0, ringKrullDim_curveLocalRing_line, ?_⟩
  have : IsDomain (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) :=
    curveLocalRingLineEquiv.toMulEquiv.isDomain
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ ?_
  have h' := congrArg curveLocalRingLineEquiv h
  rw [map_zero] at h'
  have hinj := IsLocalization.injective (Localization.AtPrime (RingHom.ker (eval (0 : Fin 1 → ℂ))))
    (M := (RingHom.ker (eval (0 : Fin 1 → ℂ))).primeCompl)
    (Ideal.primeCompl_le_nonZeroDivisors _)
  apply X_ne_zero (R := ℂ) (0 : Fin 1)
  apply hinj
  rw [map_zero]
  exact h'

end

end GroundTheory.Heights₂.Heights
