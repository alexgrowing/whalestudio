import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

namespace ReciprocityTheory.AnForm.R

open MvPolynomial OnePoint Filter Topology

noncomputable section

def projectiveLineInvPoint (w : ℂ) : OnePoint ℂ := if w = 0 then ∞ else ((w⁻¹ : ℂ) : OnePoint ℂ)

def locRingBotEquivN {n : ℕ} (p : Fin n → ℂ) :
    locPt p ≃+* locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p :=
  (RingEquiv.quotientBot (locPt p)).symm.trans (Ideal.quotEquivOfEq Ideal.map_bot.symm)

theorem ptIdeal_isMaximal {n : ℕ} (p : Fin n → ℂ) : (ptIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩

theorem locRing_bot_regularN {n : ℕ} (p : Fin n → ℂ) :
    IsRegularLocalRing (locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p) :=
  IsRegularLocalRing.of_ringEquiv (locRingBotEquivN p)

theorem locRing_bot_dimN {n : ℕ} (p : Fin n → ℂ) :
    ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p) = n := by
  have := ptIdeal_isMaximal p
  rw [← ringKrullDim_eq_of_ringEquiv (locRingBotEquivN p),
    IsLocalization.AtPrime.ringKrullDim_eq_height (ptIdeal p) (locPt p),
    (ReciprocityTheory.CA.height_maximal_mvPolynomial_field ℂ n (ptIdeal p)).2]
  rfl

theorem sub_C_eval_mem_span {n : ℕ} (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    have : f + g - C (eval p (f + g)) = (f - C (eval p f)) + (g - C (eval p g)) := by
      simp only [map_add]; ring
    rw [this]; exact add_mem hf hg
  | mul_X f i hf =>
    have : f * X i - C (eval p (f * X i)) =
        (f - C (eval p f)) * X i + C (eval p f) * (X i - C (p i)) := by
      simp only [map_mul, eval_X]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem ptIdeal_eq_span {n : ℕ} (p : Fin n → ℂ) :
    ptIdeal p = Ideal.span (Set.range fun i => X i - C (p i)) := by
  apply le_antisymm
  · intro f hf
    have h0 : eval p f = 0 := hf
    simpa [h0] using sub_C_eval_mem_span p f
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show eval p (X i - C (p i)) = 0
    simp

end

end ReciprocityTheory.AnForm.R
