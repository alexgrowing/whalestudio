import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS Finset

namespace TensK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

theorem casimir_apply' (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = ∑ a, ∑ b, E a b (E b a x) := by
  simp [casimir, LinearMap.sum_apply, Module.End.mul_apply]

theorem isGlRep_tensV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have key := LinearMap.congr_fun (hE a b c d) (f e)
  have key' : E a b (E c d (f e)) = E c d (E a b (f e)) +
      ((if b = c then E a d (f e) else 0) - (if d = a then E c b (f e) else 0)) := by
    by_cases h3 : b = c <;> by_cases h4 : d = a <;>
      simp only [h3, h4, if_true, if_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at key ⊢ <;> rw [← key] <;> abel
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    tensV_apply', map_add, apply_ite (E a b), apply_ite (E c d), map_zero, key']
  by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp only [h3, h4, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensV_apply'] <;>
    split_ifs <;> subst_vars <;> (try simp) <;> first | exact absurd rfl h4 | exact absurd rfl h3 | abel

theorem isGlRep_tensVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (tensVd E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have key := LinearMap.congr_fun (hE a b c d) (f e)
  have key' : E a b (E c d (f e)) = E c d (E a b (f e)) +
      ((if b = c then E a d (f e) else 0) - (if d = a then E c b (f e) else 0)) := by
    by_cases h3 : b = c <;> by_cases h4 : d = a <;>
      simp only [h3, h4, if_true, if_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at key ⊢ <;> rw [← key] <;> abel
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    tensVd_apply', map_sub, apply_ite (E a b), apply_ite (E c d), map_zero, key']
  by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp only [h3, h4, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensVd_apply'] <;>
    split_ifs <;> subst_vars <;> (try simp) <;> first | exact absurd rfl h4 | exact absurd rfl h3 | abel

theorem casimir_tensV' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensV E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeV E f := by
  funext e
  simp only [casimir_apply', Finset.sum_apply, tensV_apply', map_add, apply_ite (E _ _), map_zero,
    Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, eeV_apply', if_true, ite_add_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, two_smul]
  rw [Nat.cast_smul_eq_nsmul]
  abel

theorem casimir_tensVd' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensVd E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeVd E f := by
  funext e
  simp only [casimir_apply', Finset.sum_apply, tensVd_apply', map_sub, apply_ite (E _ _), map_zero,
    Finset.sum_sub_distrib, Pi.add_apply, Pi.smul_apply, eeVd_apply', if_true]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, two_smul]
  rw [Nat.cast_smul_eq_nsmul]
  abel

end TensK

theorem tens_statement (n : ℕ) : TensStatement n := by
  intro M _ _ E hE
  exact ⟨TensK.isGlRep_tensV E hE, TensK.isGlRep_tensVd E hE, TensK.casimir_tensV' E, TensK.casimir_tensVd' E⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
