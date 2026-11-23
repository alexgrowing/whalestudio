import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

namespace Formalism.CohomologicalDescent.LR

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.Symmetrization

theorem lrd_core {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℚ V]
    (φ : ι → Module.End ℚ V) (hφ : ∀ a b, Commute (φ a) (φ b)) (L : AddSubgroup V)
    (hL : ∀ (v : ι) (k : ℕ), ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • ((φ v) ^ k) x ∈ L) :
    ∀ (M : Multiset ι), ∀ x ∈ L,
      (((∏ v, (Multiset.count v M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x ∈ L := by
  suffices key : ∀ n : ℕ, ∀ M : Multiset ι, Multiset.card M = n → ∀ x ∈ L,
      (((∏ v, (Multiset.count v M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x ∈ L by
    intro M
    exact key _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hn x hx
    by_cases hM : M = 0
    · subst hM
      simp [hx]
    obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero hM

    set c := Multiset.count v M with hc
    set M' := M.filter (fun w => ¬ w = v) with hM'
    have hsplit : M = Multiset.replicate c v + M' := by
      rw [hM', hc, ← Multiset.filter_eq' M v, Multiset.filter_add_not]
    have hc0 : 0 < c := Multiset.count_pos.mpr hv
    have hcard : Multiset.card M' < n := by
      have e := congrArg Multiset.card hsplit
      rw [Multiset.card_add, Multiset.card_replicate] at e
      omega
    have hperm : M.toList.Perm (List.replicate c v ++ M'.toList) := by
      have e : (M.toList : Multiset ι) = ((List.replicate c v ++ M'.toList : List ι) : Multiset ι) := by
        rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_replicate]
        exact hsplit
      exact Multiset.coe_eq_coe.mp e
    have hpw : (M.toList.map φ).Pairwise Commute :=
      List.pairwise_map.mpr (List.pairwise_of_forall fun a b => hφ a b)
    have hprod : (M.toList.map φ).prod = φ v ^ c * (M'.toList.map φ).prod := by
      rw [(hperm.map φ).prod_eq' hpw]
      simp [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]

    have hcnt : ∀ w ∈ Finset.univ.erase v, Multiset.count w M' = Multiset.count w M := by
      intro w hw
      exact Multiset.count_filter_of_pos (Finset.ne_of_mem_erase hw)
    have hcv : Multiset.count v M' = 0 := Multiset.count_filter_of_neg (fun h => h rfl)
    have hfact : (∏ w, (Multiset.count w M).factorial : ℕ) =
        c.factorial * ∏ w, (Multiset.count w M').factorial := by
      rw [← Finset.mul_prod_erase Finset.univ (fun w => (Multiset.count w M).factorial) (Finset.mem_univ v),
        ← Finset.mul_prod_erase Finset.univ (fun w => (Multiset.count w M').factorial) (Finset.mem_univ v),
        hcv, Nat.factorial_zero, one_mul]
      congr 1
      exact Finset.prod_congr rfl fun w hw => by rw [hcnt w hw]
    have hrest := ih _ (hn ▸ hcard) M' rfl x hx
    have e : (((∏ w, (Multiset.count w M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x =
        ((c.factorial : ℚ)⁻¹) • (φ v ^ c)
          ((((∏ w, (Multiset.count w M').factorial : ℕ) : ℚ)⁻¹) • (M'.toList.map φ).prod x) := by
      rw [hprod, hfact, Module.End.mul_apply, map_smul, smul_smul, Nat.cast_mul, mul_inv]
    rw [e]
    exact hL v c _ hrest

theorem Fs_div_mem {V P R : Type} [AddCommGroup V] [Module ℚ V] [DecidableEq P] [DecidableEq R] [Fintype P]
    [Fintype R] (S : Symmetrization.HidaSetting ℚ V P R) (L : AddSubgroup V)
    (hL : ∀ (v : R × P) (k : ℕ), ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • ((S.f v) ^ k) x ∈ L) {n : ℕ}
    (m : Sym (R × P) n) : ∀ x ∈ L, ((Symmetrization.mfact m : ℚ)⁻¹) • S.Fs m x ∈ L := by
  have hcomm : ∀ a b : R × P, Commute (S.f a) (S.f b) := by
    intro a b
    have h := S.comm (Sum.inr a.1) (Sum.inl a.2) (Sum.inr b.1) (Sum.inl b.2)
    simp only [reduceCtorEq, if_false, sub_zero] at h
    exact sub_eq_zero.mp h
  intro x hx
  exact lrd_core S.f hcomm L hL m.1 x hx

end Formalism.CohomologicalDescent.LR
