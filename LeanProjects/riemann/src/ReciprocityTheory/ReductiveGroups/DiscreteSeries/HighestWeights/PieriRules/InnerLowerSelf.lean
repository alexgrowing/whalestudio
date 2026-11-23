import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KtintExpApplyOfEig

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem inner_lower_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hR : Formalism.REAL.KRel ε A) (hU : Formalism.REAL.KUnit ε A) (hw : Formalism.REAL.KHighest ε A Λ w)
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ⟪A b a w, A b a w⟫_ℂ = (((Λ a - Λ b : ℝ)) : ℂ) * ⟪w, w⟫_ℂ := by
  have hba : b ≠ a := ne_of_gt hab
  have hc := hR a b b a he he.symm
  simp only [if_true] at hc
  have hx := congrArg (fun F : Module.End ℂ V => F w) hc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw.2 a b hab he, map_zero, sub_zero] at hx
  have h1 := hU b a he.symm w (A b a w)
  rw [h1, hx, hw.1 a, hw.1 b, ← sub_smul, inner_smul_right]
  push_cast
  ring

theorem kType_dom {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : KDom ε Λ := by
  intro a b hab he
  have h := inner_lower_self (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hab he
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, T.w_norm] at h
  have h2 : ‖kunits T b a T.w‖ ^ 2 = Λ a - Λ b := by
    have h' : ((‖kunits T b a T.w‖ ^ 2 : ℝ) : ℂ) = ((Λ a - Λ b : ℝ) : ℂ) := by
      have h0 := h
      simp only [RCLike.ofReal_one, one_pow, mul_one] at h0
      simpa using h0
    exact Complex.ofReal_injective h'
  have h3 : (0 : ℝ) ≤ ‖kunits T b a T.w‖ ^ 2 := sq_nonneg _
  linarith

theorem kTypeIntDom_of
    (hint : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (_T : KType ε Λ), ∀ a, ∃ m : ℤ, Λ a = m) :
    KTypeIntDomStatement :=
  fun n ε Λ T => ⟨hint n ε Λ T, kType_dom T⟩

theorem kTypeIntDom : KTypeIntDomStatement :=
  kTypeIntDom_of fun _ _ _ T => kType_int T

end ReciprocityTheory.ChartRestriction.DS.HW
