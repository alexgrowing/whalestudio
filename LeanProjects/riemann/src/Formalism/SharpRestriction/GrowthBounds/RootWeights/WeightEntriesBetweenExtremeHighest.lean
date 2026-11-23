import Formalism.SharpRestriction.GrowthBounds.RootWeights.TraceProjectionIsInvProj

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem rootWeight_apply_first {n : ℕ} {a c : Fin n} (h : a ≠ c) : rootW a c a = 1 := by
  simp [rootW, Pi.single_apply, h]

theorem rootWeight_apply_second {n : ℕ} {a c : Fin n} (h : a ≠ c) : rootW a c c = -1 := by
  simp [rootW, Pi.single_apply, h.symm]

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem integral_operator_pow_shifts_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (a c : Fin n) (j : ℕ) : ((E a c) ^ j) x ∈ weightSp E (nu + (j : ℤ) • rootW a c) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := gl_rep_operator_weight_shift hE ih a c
    have e : nu + ((j + 1 : ℕ) : ℤ) • rootW a c = nu + (j : ℤ) • rootW a c + rootW a c := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [e]; exact h

theorem offdiag_operator_nilpotent_on_weight [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) {a c : Fin n} (hac : a ≠ c) :
    ∃ j : ℕ, ((E a c) ^ j) x = 0 := by
  obtain ⟨F, hF⟩ := findim_exists_finite_weights E hE.2.2
  by_contra hcon
  push Not at hcon
  have hin : ∀ j : ℕ, nu + (j : ℤ) • rootW a c ∈ F := by
    intro j
    by_contra hj
    exact hcon j (weight_support_sum_eq_zero (O := O) E (fun mu => mu ∈ F) (integral_operator_pow_shifts_weight hE hx a c j) (hF Submodule.mem_top) hj)
  have hinj : Function.Injective (fun j : ℕ => (⟨nu + (j : ℤ) • rootW a c, hin j⟩ : F)) := by
    intro i j hij
    have h1 := congrFun (congrArg Subtype.val hij) a
    simp only [Pi.add_apply, Pi.smul_apply, rootWeight_apply_first hac, smul_eq_mul, mul_one] at h1
    omega
  exact not_injective_infinite_finite _ hinj

theorem offdiag_string_reaches_top_nonzero [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) {a c : Fin n} (hac : a ≠ c) :
    ∃ j : ℕ, ((E a c) ^ j) x ≠ 0 ∧ E a c (((E a c) ^ j) x) = 0 := by
  obtain ⟨j, h1, h2⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists (p := fun j => ((E a c) ^ j) x = 0)
    (by simpa using h0) (offdiag_operator_nilpotent_on_weight hE hx hac)
  refine ⟨j, h1, ?_⟩
  rw [pow_succ', Module.End.mul_apply] at h2
  exact h2

theorem weight_entries_between_extreme_highest [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (h0 : x ≠ 0) (a : Fin n) : lam (lastIdx n) ≤ nu a ∧ nu a ≤ lam 0 := by
  constructor
  · by_cases ha : a = lastIdx n
    · subst ha; exact (irreducible_weight_end_bounds hI hx h0).2
    · have hla : lastIdx n ≠ a := fun e => ha e.symm
      obtain ⟨j, h1, h2⟩ := offdiag_string_reaches_top_nonzero hI.1 hx h0 hla
      have hw := integral_operator_pow_shifts_weight hI.1 hx (lastIdx n) a j
      obtain ⟨m, hm, h3, -⟩ := sl2_string_nonvanishing hI.1.1 hla h1 hw h2
      have hz := (irreducible_weight_end_bounds hI (integral_operator_pow_shifts_weight hI.1 hw a (lastIdx n) m) h3).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rootWeight_apply_first hla, rootWeight_apply_second hla, rootWeight_apply_second ha] at hm hz
      omega
  · by_cases ha : a = 0
    · subst ha; exact (irreducible_weight_end_bounds hI hx h0).1
    · obtain ⟨j, h1, h2⟩ := offdiag_string_reaches_top_nonzero hI.1 hx h0 ha
      have hw := integral_operator_pow_shifts_weight hI.1 hx a 0 j
      obtain ⟨m, hm, h3, -⟩ := sl2_string_nonvanishing hI.1.1 ha h1 hw h2
      have h0a : (0 : Fin n) ≠ a := fun e => ha e.symm
      have hz := (irreducible_weight_end_bounds hI (integral_operator_pow_shifts_weight hI.1 hw 0 a m) h3).1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rootWeight_apply_first ha, rootWeight_apply_second ha, rootWeight_apply_first h0a] at hm hz
      omega

end hw

end Formalism.MainNotions.G.GLWeightTheory
