import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.CountC

open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

theorem eiii_factor {g : ℕ} [Fact g.Prime] {r : ℕ} (c : (ZMod g)ˣ) {f : (ZMod g)[X]}
    (hf : Eiii g r c f) :
    ∃ P, Good c P ∧ P ∣ f ∧ 1 ≤ P.natDegree ∧ P.natDegree ≤ r := by
  obtain ⟨hlab, -, hneg⟩ := hf
  push Not at hneg
  obtain ⟨ℓ, hℓ, -, x, hx, hxc⟩ := hneg
  have hf0 : f ≠ 0 := hlab.1.ne_zero
  have hxroot : aeval x f = 0 := by
    unfold rootsBar at hx
    rw [mem_roots_map hf0] at hx
    rw [aeval_def]; exact hx
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hPd : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hint
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, aeval_def, eval₂_at_zero] at hxroot
    exact hlab.2.2 ((_root_.map_eq_zero_iff _ (algebraMap (ZMod g) (Fbar g)).injective).1 hxroot)
  have hfix := frob_fix x
  have hg2 := (Fact.out : g.Prime).two_le
  have hpos : 1 ≤ g ^ (minpoly (ZMod g) x).natDegree := Nat.one_le_pow _ _ (by omega)
  have hgk : g ≤ g ^ (minpoly (ZMod g) x).natDegree := Nat.le_self_pow (by omega) g
  have hxo : 0 < orderOf x := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨g ^ (minpoly (ZMod g) x).natDegree - 1, by omega, ?_⟩
    have h2 : x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
    exact mul_right_cancel₀ hx0 h2
  have hco : 0 < orderOf (algebraMap (ZMod g) (Fbar g) (c : ZMod g)) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨g - 1, by omega, ?_⟩
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one]
  obtain ⟨j, hj⟩ := ptp_eq_imp ℓ hℓ x _ hxo hco hxc
  refine ⟨minpoly (ZMod g) x, ⟨minpoly.monic hint, minpoly.irreducible hint, ℓ, hℓ, j,
    minpoly.dvd _ _ ?_⟩, minpoly.dvd _ _ hxroot, hPd, ?_⟩
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [hj, sub_self]
  · have := natDegree_le_of_dvd (minpoly.dvd _ _ hxroot) hf0
    rw [hlab.2.1] at this
    exact this

theorem countP : CountP := by
  intro g r _ hg hr c T hT
  classical
  have hex : ∀ f ∈ T, ∃ P, Good c P ∧ P ∣ f ∧ 1 ≤ P.natDegree ∧ P.natDegree ≤ r :=
    fun f hf => eiii_factor c (hT f hf)
  choose! Pf hPf using hex
  have hlab : ∀ f ∈ T, IsLab g r f := fun f hf => (hT f hf).1
  have h1 : T.card ≤ ∑ P ∈ T.image Pf, g ^ (r - P.natDegree) := by
    rw [Finset.card_eq_sum_card_image Pf T]
    refine Finset.sum_le_sum (fun P hP => ?_)
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP
    refine le_trans (Finset.card_le_card ?_) (count_mult r T hlab (Pf f0) (hPf f0 hf0).1.1)
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨hf.1, hf.2 ▸ (hPf f hf.1).2.1⟩
  have hmaps : ∀ P ∈ T.image Pf, P.natDegree ∈ Finset.Icc 1 r := by
    intro P hP
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP
    exact Finset.mem_Icc.2 ⟨(hPf f0 hf0).2.2.1, (hPf f0 hf0).2.2.2⟩
  have h2 : ∑ P ∈ T.image Pf, g ^ (r - P.natDegree) = ∑ k ∈ Finset.Icc 1 r,
      ((T.image Pf).filter (fun P => P.natDegree = k)).card * g ^ (r - k) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.1 hP).2]),
      Finset.sum_const, smul_eq_mul]
  have h3 : ∀ k ∈ Finset.Icc 1 r,
      k * ((T.image Pf).filter (fun P => P.natDegree = k)).card ≤ ppSum (g ^ k - 1) := by
    intro k hk
    refine count_good c hg k (Finset.mem_Icc.1 hk).1 _ (fun P hP => ?_)
    rw [Finset.mem_filter] at hP
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP.1
    exact ⟨(hPf f0 hf0).1, hP.2⟩
  have h12 : (T.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 r,
      (((T.image Pf).filter (fun P => P.natDegree = k)).card : ℝ) * (g : ℝ) ^ (r - k) := by
    have := h1.trans h2.le
    exact_mod_cast this
  refine h12.trans (Finset.sum_le_sum (fun k hk => ?_))
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [le_div_iff₀ (by linarith)]
  have := h3 k hk
  rw [mul_comm]
  exact_mod_cast this

end PI.SqfRootShift.W
