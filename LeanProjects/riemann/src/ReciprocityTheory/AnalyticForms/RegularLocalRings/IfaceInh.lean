import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

theorem ptIdeal_fin_zero (p : Fin 0 → ℂ) : ptIdeal p = ⊥ := by
  ext f
  simp only [ptIdeal, RingHom.mem_ker, Ideal.mem_bot]
  constructor
  · intro h
    rw [MvPolynomial.eq_C_of_isEmpty f] at h ⊢
    simpa using h
  · rintro rfl
    simp

instance isRegularRing_fin_zero : IsRegularRing (MvPolynomial (Fin 0) ℂ) :=
  IsRegularRing.of_ringEquiv (isEmptyRingEquiv ℂ (Fin 0)).symm

def locRingBotEquiv (p : Fin 0 → ℂ) : locPt p ≃+* locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p :=
  (RingEquiv.quotientBot (locPt p)).symm.trans (Ideal.quotEquivOfEq Ideal.map_bot.symm)

private theorem locRing_bot_fin_zero_regular_and_dim_zero (p : Fin 0 → ℂ) :
    IsRegularLocalRing (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) ∧
      ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) = ((0 - 0 : ℕ) : WithBot ℕ∞) := by
  refine isRegularLocalRing_of_jacobian (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p ?_
    (fun i : Fin 0 => i.elim0) (fun i => i.elim0) linearIndependent_empty_type ?_
  · intro h hh
    rw [Ideal.mem_bot] at hh
    simp [hh]
  · refine ⟨⊥, ?_, bot_le, by simp⟩
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

theorem locRing_bot_regular (p : Fin 0 → ℂ) :
    IsRegularLocalRing (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) := (locRing_bot_fin_zero_regular_and_dim_zero p).1

theorem locRing_bot_dim (p : Fin 0 → ℂ) :
    ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p) = 0 := by
  simpa using (locRing_bot_fin_zero_regular_and_dim_zero p).2

end

end ReciprocityTheory.AnForm.R
