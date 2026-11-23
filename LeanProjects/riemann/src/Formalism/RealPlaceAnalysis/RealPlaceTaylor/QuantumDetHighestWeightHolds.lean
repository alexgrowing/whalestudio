import Formalism.RealPlaceAnalysis.StatementE

open Finset

noncomputable section

namespace Formalism.REAL

theorem shiftedGenerator_eq_smul_add {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (r : ℂ)
    (p q : Fin n) : Tm E r p q = (if p = q then r else 0) • (1 : A) + E p q := by
  unfold Tm
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]

theorem rttRelation : RTT := by
  intro A _ _ n E hE x y a b c d
  have h' : E a b * E c d = E c d * E a b + ((if c = b then E a d else 0) - (if a = d then E c b else 0)) := by
    have h0 := hE a b c d
    simp only [@eq_comm _ b c, @eq_comm _ d a] at h0
    rw [← h0]
    abel
  simp only [shiftedGenerator_eq_smul_add, Algebra.algebraMap_eq_smul_one]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
    smul_add, smul_sub]
  rw [h']
  split_ifs <;> module

theorem quantumMinorRowSkew_holds : QSkewRow := by
  intro A _ _ n t E a b τ u
  unfold qminor
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulLeft]
  have hs : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign (τ * σ) : ℤ) : A) =
      ((Equiv.Perm.sign σ : ℤ) : A) := by
    rw [← Int.cast_mul, Equiv.Perm.sign_mul, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [← mul_assoc, hs]
  rfl

theorem prod_ofFn_apply_of_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V),
      (∀ k, F k v = c k • v) → (List.ofFn F).prod v = (∏ k, c k) • v := by
  intro m
  induction m with
  | zero => intro F c v _; simp
  | succ m ih =>
    intro F c v h
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      ih (fun i => F i.succ) (fun i => c i.succ) v (fun i => h i.succ), map_smul, h 0, smul_smul,
      Fin.prod_univ_succ, mul_comm (c 0)]

theorem prod_ofFn_apply_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V) (j : Fin m),
      F j v = 0 → (∀ k, j < k → F k v = c k • v) → (List.ofFn F).prod v = 0 := by
  intro m
  induction m with
  | zero => intro F c v j; exact j.elim0
  | succ m ih =>
    intro F c v j hj hk
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    cases j using Fin.cases with
    | zero =>
      rw [prod_ofFn_apply_of_eigen m (fun i => F i.succ) (fun i => c i.succ) v (fun i => hk i.succ (Fin.succ_pos i)),
        map_smul, hj, smul_zero]
    | succ j' =>
      rw [ih (fun i => F i.succ) (fun i => c i.succ) v j' hj
        (fun i hi => hk i.succ (Fin.succ_lt_succ_iff.mpr hi)), map_zero]

theorem quantumDetHighestWeight_holds : QDetHW := by
  intro V _ _ n E ν v hE hv u
  obtain ⟨hdiag, hup⟩ := hv
  have hdiag' : ∀ k : Fin n, Tm E (u - (k : ℂ)) k k v = (u - (k : ℂ) + ν k) • v := by
    intro k
    rw [Tm, if_pos rfl, LinearMap.add_apply, Module.algebraMap_end_apply, hdiag k, add_smul]
  have hoff : ∀ j k : Fin n, j < k → Tm E (u - (k : ℂ)) j k v = 0 := by
    intro j k hjk
    simp [Tm, ne_of_lt hjk, hup j k hjk]
  unfold qdet qminor
  rw [LinearMap.sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, id_eq, Equiv.Perm.one_apply]
    exact prod_ofFn_apply_of_eigen n _ _ v hdiag'
  · intro σ _ hσ
    have hne : (Finset.univ.filter fun k => σ k ≠ k).Nonempty := by
      by_contra hc
      apply hσ
      refine Equiv.ext fun k => ?_
      by_contra hk
      exact hc ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    set j := (Finset.univ.filter fun k => σ k ≠ k).max' hne with hj
    have hjmove : σ j ≠ j := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hfix : ∀ k, j < k → σ k = k := by
      intro k hk
      by_contra h
      have := Finset.le_max' (Finset.univ.filter fun k => σ k ≠ k) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact (not_lt.mpr this) hk
    have hlt : σ j < j := by
      rcases lt_or_gt_of_ne hjmove with h | h
      · exact h
      · exact absurd (σ.injective (hfix (σ j) h)) hjmove
    have hP : (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod v = 0 := by
      apply prod_ofFn_apply_eq_zero n _ (fun k => u - (k : ℂ) + ν k) v j
      · exact hoff _ _ hlt
      · intro k hk
        simp only [id_eq, hfix k hk]
        exact hdiag' k
    rw [Module.End.mul_apply, hP, map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end Formalism.REAL
