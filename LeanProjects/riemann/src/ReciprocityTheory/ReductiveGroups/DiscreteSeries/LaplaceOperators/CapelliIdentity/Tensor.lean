import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Expand

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tensV_apply' {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M)
    (e : Fin n) : tensV E a b f e = E a b (f e) + if e = a then f b else 0 := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  split_ifs <;> simp

theorem tensVd_apply' {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M)
    (e : Fin n) : tensVd E a b f e = E a b (f e) - if e = b then f a else 0 := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  split_ifs <;> simp

theorem eeV_apply' {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (b : Fin n) :
    eeV E f b = ∑ a, E a b (f a) := by
  simp [eeV, LinearMap.pi_apply, LinearMap.sum_apply]

theorem eeVd_apply' {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (a : Fin n) :
    eeVd E f a = -∑ c, E a c (f c) := by
  simp [eeVd, LinearMap.pi_apply, LinearMap.sum_apply]

theorem isGlRep_tensV {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) :
    IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have h := LinearMap.congr_fun (hE a b c d) (f e)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, tensV_apply', map_add, Pi.sub_apply]
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp only [hbc, hda, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensV_apply'] at h ⊢ <;>
    split_ifs <;> simp_all <;> (rw [← sub_eq_zero] at h ⊢; convert h using 1; abel)

theorem isGlRep_tensVd {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) :
    IsGlRep (tensVd E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have h := LinearMap.congr_fun (hE a b c d) (f e)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, tensVd_apply', map_sub, Pi.sub_apply]
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp only [hbc, hda, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensVd_apply'] at h ⊢ <;>
    split_ifs <;> simp_all <;> (rw [← sub_eq_zero] at h ⊢; convert h using 1; abel)

theorem casimir_tensV {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensV E) f = (fun d => casimir E (f d)) + ((n : ℂ) • f + (2 : ℂ) • eeV E f) := by
  funext e
  simp only [casimir, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, tensV_apply', map_add,
    Pi.add_apply, Pi.smul_apply, eeV_apply', Finset.sum_add_distrib]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hx : ∀ g : Fin n → Fin n → M, (∑ x, ∑ x_1, if e = x then g x x_1 else 0) = ∑ x_1, g e x_1 := by
    intro g
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hx]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul, two_smul]
  abel

theorem casimir_tensVd {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensVd E) f = (fun d => casimir E (f d)) + ((n : ℂ) • f + (2 : ℂ) • eeVd E f) := by
  funext e
  simp only [casimir, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, tensVd_apply', map_sub,
    Pi.add_apply, Pi.smul_apply, eeVd_apply', Finset.sum_sub_distrib]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hx : ∀ g : Fin n → Fin n → M, (∑ x, ∑ x_1, if e = x then g x x_1 else 0) = ∑ x_1, g e x_1 := by
    intro g
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hx]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul, two_smul]
  abel

theorem eeV_nnPlus {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E)
    (y : Fin (m + 1) → ℂ) (om : ℂ) (v : M) (hv : capelliC E om v = 0) :
    eeV E (nnPlus E y om v) = (-om) • nnPlus E y om v := by
  have hE' : GlRelR E := hE
  funext b
  have key : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      E d b (cminor E d.succAbove c.succAbove (om - 1) v) =
      (-(om * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ)))) • cminor E b.succAbove c.succAbove (om - 1) v := by
    intro c
    have h := LinearMap.congr_fun (capelli_expand_plus E hE' om b c) v
    have hr : (if b = c then capelliC E om else 0) v = 0 := by split_ifs <;> simp [hv]
    rw [hr, LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, Module.End.mul_apply, capEntry, LinearMap.add_apply, smul_add,
      Finset.sum_add_distrib] at h
    have h2 : ∑ x : Fin (m + 1), ((-1 : ℂ) ^ ((x : ℕ) + (c : ℕ))) •
        (if x = b then algebraMap ℂ (Module.End ℂ M) om else 0) (cminor E x.succAbove c.succAbove (om - 1) v) =
        (om * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor E b.succAbove c.succAbove (om - 1) v := by
      rw [Finset.sum_eq_single b]
      · simp [Module.algebraMap_end_apply, smul_smul, mul_comm]
      · intro d _ hd; simp [hd]
      · simp
    rw [h2] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h
  rw [eeV_apply', Pi.smul_apply]
  simp only [nnPlus, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  calc _ = y c • ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) •
        E a b (cminor E a.succAbove c.succAbove (om - 1) v) := by
        rw [Finset.smul_sum]; simp only [smul_smul]
    _ = _ := by rw [key c, smul_smul, smul_smul]; congr 1; ring

theorem eeVd_nnMinus {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E)
    (β : Fin (m + 1) → ℂ) (om : ℂ) (v : M) (hv : capelliC E om v = 0) :
    eeVd E (nnMinus E β om v) = (om - (m : ℂ)) • nnMinus E β om v := by
  have hE' : GlRelR E := hE
  funext a
  have key : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      E a d (cminor E c.succAbove d.succAbove om v) =
      (-((om - (m : ℂ)) * (-1 : ℂ) ^ ((a : ℕ) + (c : ℕ)))) • cminor E c.succAbove a.succAbove om v := by
    intro c
    have h := LinearMap.congr_fun (capelli_expand_minus E hE' om a c) v
    have hr : (if a = c then capelliC E om else 0) v = 0 := by split_ifs <;> simp [hv]
    rw [hr, LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, Module.End.mul_apply, capEntry, LinearMap.add_apply, smul_add,
      Finset.sum_add_distrib] at h
    have h2 : ∑ x : Fin (m + 1), ((-1 : ℂ) ^ ((x : ℕ) + (c : ℕ))) •
        (if a = x then algebraMap ℂ (Module.End ℂ M) (om - (m : ℂ)) else 0) (cminor E c.succAbove x.succAbove om v) =
        ((om - (m : ℂ)) * (-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) • cminor E c.succAbove a.succAbove om v := by
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, Module.algebraMap_end_apply, smul_smul, mul_comm]
      · intro d _ hd; simp [Ne.symm hd]
      · simp
    rw [h2] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h
  rw [eeVd_apply', Pi.smul_apply]
  simp only [nnMinus, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  calc _ = -(β c • ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        E a d (cminor E c.succAbove d.succAbove om v)) := by
        rw [Finset.smul_sum]; simp only [smul_smul]
    _ = _ := by rw [key c, smul_smul, smul_smul, ← neg_smul]; congr 1; ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
