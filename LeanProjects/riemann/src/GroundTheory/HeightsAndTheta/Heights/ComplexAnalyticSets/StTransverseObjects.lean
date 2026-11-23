import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

noncomputable section

class IsCohenMacaulayLocalRing (B : Type*) [CommRing B] : Prop extends IsLocalRing B, IsNoetherianRing B where
  exists_isWeaklyRegular : ∃ rs : List B, (∀ r ∈ rs, r ∈ maximalIdeal B) ∧
    RingTheory.Sequence.IsWeaklyRegular B rs ∧ ringKrullDim B = (rs.length : WithBot ℕ∞)

theorem isCohenMacaulayLocalRing_of_field (K : Type*) [Field K] : IsCohenMacaulayLocalRing K where
  exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil K K, by
    simp [ringKrullDim_eq_zero_of_field]⟩

variable {n d : ℕ}

instance isMaximal_ker_eval_point (q : Fin n → ℂ) :
    (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun z => ⟨C z, eval_C z⟩

abbrev localRingAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))

def IsCohenMacaulayAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Prop :=
  IsCohenMacaulayLocalRing (localRingAt I q)

theorem isCohenMacaulayAt_point (q : Fin n → ℂ) :
    IsCohenMacaulayAt (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) q := by
  unfold IsCohenMacaulayAt localRingAt
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  let _ := Ideal.Quotient.field
    (maximalIdeal (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))
  exact isCohenMacaulayLocalRing_of_field _

theorem not_isCohenMacaulayAt_top (q : Fin n → ℂ) :
    ¬ IsCohenMacaulayAt (⊤ : Ideal (MvPolynomial (Fin n) ℂ)) q := by
  intro h
  unfold IsCohenMacaulayAt localRingAt at h
  rw [Ideal.map_top] at h
  have hs : Subsingleton (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
      (⊤ : Ideal (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  obtain ⟨a, b, hab⟩ := h.toIsLocalRing.toNontrivial.exists_pair_ne
  exact hab (Subsingleton.elim a b)

def IsTransverseSliceAt (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) :
    Prop :=
  ∀ g : MvPolynomial (Fin n) ℂ, eval q g = 0 → ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧ s * g ∈ sliceIdeal W L q

theorem isTransverseSliceAt_line :
    IsTransverseSliceAt (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  intro g hg
  refine ⟨1, by simp, ?_⟩
  rw [one_mul]
  refine Ideal.mem_sup_right ?_
  have hX : linPoly (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 - C (((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ 0) 0) = X 0 := by
    simp [linPoly]
  have hspan : Ideal.span (X '' (Set.univ : Set (Fin 1))) ≤
      Ideal.span (Set.range fun i : Fin 1 =>
        linPoly (1 : Matrix (Fin 1) (Fin 1) ℂ) i - C (((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ 0) i)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    refine Ideal.subset_span ⟨i, ?_⟩
    dsimp only
    rw [Subsingleton.elim i 0, hX]
  refine hspan (MvPolynomial.mem_ideal_span_X_image.mpr fun m hm => ?_)
  refine ⟨0, Set.mem_univ _, fun h0 => ?_⟩
  have hm0 : m = 0 := Finsupp.ext fun i => by rw [Subsingleton.elim i 0, h0]; rfl
  subst hm0
  rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero] at hm
  exact hm hg

theorem not_isTransverseSliceAt_zero :
    ¬ IsTransverseSliceAt (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  intro h
  obtain ⟨s, hs, hsX⟩ := h (X 0) (by simp)
  have hbot : sliceIdeal (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 = ⊥ := by
    refine le_bot_iff.mp (sup_le le_rfl ?_)
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [linPoly]
  rw [hbot, Ideal.mem_bot, mul_eq_zero] at hsX
  rcases hsX with h0 | h0
  · exact hs (by rw [h0, map_zero])
  · exact X_ne_zero 0 h0

end

end GroundTheory.Heights₂.Heights
