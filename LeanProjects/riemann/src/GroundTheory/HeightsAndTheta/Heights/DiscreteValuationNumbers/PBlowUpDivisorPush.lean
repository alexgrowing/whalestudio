import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Pullback

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem liftForm_mem_blowUpOf_of_mem (P : Ideal (MRing ι R)) (u : J → MRing ι R) {p : MRing ι R}
    (hp : p ∈ P) : liftForm (J := J) p ∈ blowUpOf P u := by
  let φ : MRing ι R →ₐ[R] Polynomial (MRing ι R ⧸ P) :=
    (Polynomial.CAlgHom (R := R) (A := MRing ι R ⧸ P)).comp (Ideal.Quotient.mkₐ R P)
  have hcomp : (aeval (blowUpSubst P u)).comp (liftForm (ι := ι) (J := J) (R := R)) = φ := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, liftForm, rename_X, aeval_X]
    rfl
  have h := DFunLike.congr_fun hcomp p
  rw [AlgHom.comp_apply] at h
  unfold blowUpOf
  rw [RingHom.mem_ker, h]
  show Polynomial.C (Ideal.Quotient.mk P p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

end Pullback

section Sums

open Classical in

theorem finsum_sub_mul_eq_of_support {α : Type*} (Z₁ Z₂ n : α → ℤ) (p : α → Prop)
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite)
    (hv : ∀ W, Z₁ W - Z₂ W ≠ 0 → p W) :
    ∑ᶠ W, (Z₁ W - Z₂ W) * n W =
      ∑ᶠ W, Z₁ W * (if p W then n W else 0) - ∑ᶠ W, Z₂ W * (if p W then n W else 0) := by
  have e : ∀ W, (Z₁ W - Z₂ W) * n W =
      Z₁ W * (if p W then n W else 0) - Z₂ W * (if p W then n W else 0) := by
    intro W
    by_cases h : Z₁ W - Z₂ W = 0
    · rw [h, zero_mul, sub_eq_zero.mp h, sub_self]
    · rw [if_pos (hv W h), ← sub_mul]
  rw [finsum_congr e, finsum_sub_distrib]
  · exact h₁.subset fun W hW => left_ne_zero_of_mul hW
  · exact h₂.subset fun W hW => left_ne_zero_of_mul hW

end Sums

theorem BlowUpDivisorPush.proof (hvert : BlowUpVerticalPush.Statement.{u}) :
    BlowUpDivisorPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP b f g hD N u hu hu' a
  have hfin := DivCycleFiniteSupport.proof.{u}
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees

  have hvertB : ∀ W, divCycle (blowUpOf P u) (liftForm (J := J) f) W -
      divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 → (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W hW
    by_contra hϖW
    have hsupp : W.IsPrime ∧ blowUpOf P u ≤ W ∧ IsRelevant W := by
      by_cases h1 : divCycle (blowUpOf P u) (liftForm (J := J) f) W = 0
      · have h2 : divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 := by
          intro h2; apply hW; rw [h1, h2, sub_zero]
        exact le_and_isRelevant_of_divCycle_ne_zero h2
      · exact le_and_isRelevant_of_divCycle_ne_zero h1
    obtain ⟨hWp, hBW, hWrel⟩ := hsupp
    let W₀ : Ideal (MRing ι O) := W.comap (liftForm (ι := ι) (J := J) (R := O))
    have hW₀ : W₀.IsPrime := Ideal.comap_isPrime _ _
    have hPW₀ : P ≤ W₀ := fun p hp => hBW (liftForm_mem_blowUpOf_of_mem P u hp)
    have hrel₀ : IsRelevant W₀ := by
      intro k
      obtain ⟨i, hi⟩ := hWrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have h' : liftForm (ι := ι) (J := J) (R := O) (X ⟨k, i⟩) ∈ W := h
      rwa [liftForm, rename_X] at h'
    have hϖ₀ : (C ϖ : MRing ι O) ∉ W₀ := by
      intro h
      have h' : liftForm (ι := ι) (J := J) (R := O) (C ϖ) ∈ W := h
      rw [liftForm, rename_C] at h'
      exact hϖW h'
    obtain ⟨s, t, hs, ht, hst⟩ := hD.unit_off_special W₀ hW₀ hPW₀ hrel₀ hϖ₀
    apply hW
    rw [divCycle_eq_of_mul_sub_mem (u := liftForm (J := J) s) (v := liftForm (J := J) t) hs ht ?_,
      sub_self]
    have := liftForm_mem_blowUpOf_of_mem (J := J) P u hst
    rwa [map_sub, map_mul, map_mul] at this
  have e₁ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bf f hbf hD.num_not_mem a
  have e₂ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bg g hbg hD.den_not_mem a
  unfold cycEval at e₁ e₂
  unfold cycEval ratDiv
  rw [finsum_sub_mul_eq_of_support (divCycle (blowUpOf P u) (liftForm (J := J) f))
      (divCycle (blowUpOf P u) (liftForm (J := J) g)) _ _ (hfin _ _ _ _ _) (hfin _ _ _ _ _) hvertB,
    finsum_sub_mul_eq_of_support (divCycle P f) (divCycle P g) _ _ (hfin _ _ _ _ _)
      (hfin _ _ _ _ _) hD.vertical, e₁, e₂]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
