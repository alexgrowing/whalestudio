import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem ll3 : StatLL3 := by
  intro ℓ hℓ s H0 h d U a b hh hH hU ha hab hb hd
  have := Fact.mk hℓ
  have hn0 : n0 ℓ H0 ≤ Nat.log ℓ (2 * h) + 1 := by
    apply Nat.sInf_le
    show H0 ≤ ℓ ^ (Nat.log ℓ (2 * h) + 1) * (ℓ - 1)
    have h1 : 2 * h < ℓ ^ (Nat.log ℓ (2 * h) + 1) := Nat.lt_pow_succ_log_self hℓ.one_lt _
    have h2 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    nlinarith
  refine ⟨by unfold mOf; omega, ?_⟩
  generalize mOf ℓ s H0 = m at hd ⊢
  have hr : ∀ i ∈ Finset.Ico a b, rI ℓ m U i ≤ U.card * (m + Nat.log ℓ (2 * h)) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold rI
    calc ∑ u ∈ U.erase i, (m + padicValInt ℓ (u - i))
        ≤ (U.erase i).card • (m + Nat.log ℓ (2 * h)) := by
          apply Finset.sum_le_card_nsmul
          intro u hu
          have hu' := hU u (Finset.mem_of_mem_erase hu)
          have h1 : padicValInt ℓ (u - i) ≤ Nat.log ℓ (2 * h) := by
            unfold padicValInt
            refine le_trans (padicValNat_le_nat_log _) (Nat.log_mono_right ?_)
            omega
          omega
      _ ≤ U.card * (m + Nat.log ℓ (2 * h)) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_erase_le)
  have hc : cM ℓ m U a b ≤ (b - a).toNat * (3 + U.card * (m + Nat.log ℓ (2 * h))) := by
    unfold cM
    calc ∑ i ∈ Finset.Ico a b, (2 + max 1 (rI ℓ m U i))
        ≤ (Finset.Ico a b).card • (3 + U.card * (m + Nat.log ℓ (2 * h))) := by
          apply Finset.sum_le_card_nsmul
          intro i hi
          have := hr i hi
          omega
      _ = _ := by rw [Int.card_Ico, smul_eq_mul]
  unfold cLL
  omega

theorem filtPow : StatFiltPow := by
  intro ℓ hℓ N _ F γ hF0 hanti hstep b hb x

  set M := ℓ ^ (b - 1) with hM
  let P : AddSubgroup N := (nsmulAddMonoidHom (α := N) (ℓ ^ 2)).range ⊔ F M
  have hP : ∀ v ∈ P, ∃ y : N, ∃ z ∈ F M, v = (ℓ ^ 2) • y + z := by
    intro v hv
    obtain ⟨p, ⟨y, rfl⟩, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    exact ⟨y, z, hz, rfl⟩
  apply hP
  let G : Module.End ℤ N := γ.toIntLinearMap
  let Y : Module.End ℤ N := G - 1
  have hY : ∀ v, Y v = γ v - v := fun v => by simp [Y, G]
  have hYk : ∀ k, (Y ^ k) x ∈ F k := by
    intro k
    induction k with
    | zero => rw [hF0]; trivial
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, hY]
      exact hstep k _ ih
  have hmono : ∀ k, M ≤ k → F k ≤ F M := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_refl _
    | succ k _ ih => exact le_trans (hanti k) ih
  have hγ : G = Y + 1 := by simp [Y]
  have hpow : (⇑γ)^[ℓ ^ b] x = ((Y + 1) ^ (ℓ ^ b)) x := by
    rw [← hγ, Module.End.pow_apply]; rfl
  rw [hpow, (Commute.one_right Y).add_pow, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  rw [LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_right, LinearMap.sum_apply]
  apply AddSubgroup.sum_mem
  intro k _
  have hterm : (Y ^ (k + 1) * ((ℓ ^ b).choose (k + 1) : Module.End ℤ N)) x
      = ((ℓ ^ b).choose (k + 1)) • (Y ^ (k + 1)) x := by
    rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
  rw [hterm]
  by_cases hk : k + 1 < M
  · obtain ⟨t, ht⟩ := binom ℓ hℓ b (k + 1) hb (Nat.succ_pos k) hk
    apply AddSubgroup.mem_sup_left
    refine ⟨t • (Y ^ (k + 1)) x, ?_⟩
    rw [ht, mul_smul]; rfl
  · apply AddSubgroup.mem_sup_right
    exact (F M).nsmul_mem (hmono _ (by omega) (hYk _)) _

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
