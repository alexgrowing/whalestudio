import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Per
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PadicShift

theorem exists_period (p : ℕ) [Fact p.Prime] {N : Type} (f : ℤ_[p] → N)
    (hf : IsLocallyConstant f) :
    ∃ m : ℕ, ∀ x y : ℤ_[p], ((p : ℤ_[p]) ^ m) ∣ x - y → f x = f y := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric (s := (Set.univ : Set ℤ_[p]))
    (c := fun v : N => f ⁻¹' {v}) isCompact_univ (fun v => hf.isOpen_fiber v)
    (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ hp)
  refine ⟨m, fun x y hxy => ?_⟩
  obtain ⟨i, hi⟩ := h x (Set.mem_univ _)
  have hx : f x = i := hi (Metric.mem_ball_self hδ)
  have hy : f y = i := by
    apply hi
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    have : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ m} := Ideal.mem_span_singleton.2 hxy
    have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) m).2 this
    refine lt_of_le_of_lt h2 (lt_of_eq_of_lt ?_ hm)
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hx, hy]

theorem sum_periodic {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (hg : ∀ i, g (i + P) = g i) (k : ℕ) :
    ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i :=
  _root_.UpperTheory.Reformulated.B.Yra7.main g P hg k

theorem isLocallyConstant_toZModPow (p : ℕ) [Fact p.Prime] (M : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) M) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨Metric.closedBall x ((p : ℝ) ^ (-(M : ℤ))),
    IsUltrametricDist.isOpen_closedBall _ (zpow_pos hp _).ne',
    Metric.mem_closedBall_self (zpow_pos hp _).le, fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) M).1 hy
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  exact h1

theorem val_toZModPow_dvd (p : ℕ) [Fact p.Prime] (M : ℕ) (z : ℤ_[p]) :
    ((p : ℤ_[p]) ^ M) ∣ z - (((PadicInt.toZModPow (p := p) M z).val : ℕ) : ℤ_[p]) := by
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_self]

theorem exists_primitive (p : ℕ) [Fact p.Prime] {N : Type} [AddCommGroup N] (n : ℕ)
    (hN : ∀ x : N, p ^ n • x = 0) (f : ℤ_[p] → N) (hf : IsLocallyConstant f) :
    ∃ y : ℤ_[p] → N, IsLocallyConstant y ∧ ∀ z, y (z + 1) - y z = f z := by
  obtain ⟨m, hm⟩ := exists_period p f hf
  set M := n + m with hM
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let g : ℕ → N := fun i => f (i : ℤ_[p])
  have hper : ∀ i, g (i + p ^ m) = g i := by
    intro i
    apply hm
    refine ⟨1, ?_⟩
    push_cast
    ring
  have hsum : ∑ i ∈ Finset.range (p ^ M), g i = 0 := by
    rw [hM, pow_add, sum_periodic g (p ^ m) hper (p ^ n), hN]
  have hfg : ∀ z, f z = g (PadicInt.toZModPow (p := p) M z).val := by
    intro z
    apply hm
    exact (pow_dvd_pow _ (Nat.le_add_left m n)).trans (val_toZModPow_dvd p M z)
  refine ⟨fun z => ∑ i ∈ Finset.range (PadicInt.toZModPow (p := p) M z).val, g i,
    (isLocallyConstant_toZModPow p M).comp
      (fun a => ∑ i ∈ Finset.range a.val, g i), fun z => ?_⟩
  have hv : (PadicInt.toZModPow (p := p) M z).val < p ^ M := ZMod.val_lt _
  have hval : (PadicInt.toZModPow (p := p) M (z + 1)).val
      = ((PadicInt.toZModPow (p := p) M z).val + 1) % p ^ M := by
    rw [map_add, map_one, ← ZMod.val_natCast]
    push_cast
    rw [ZMod.natCast_zmod_val]
  simp only [hval]
  rw [hfg z]
  generalize (PadicInt.toZModPow (p := p) M z).val = v at hv
  rcases Nat.lt_or_ge (v + 1) (p ^ M) with h | h
  · rw [Nat.mod_eq_of_lt h, Finset.sum_range_succ, add_sub_cancel_left]
  · have hv1 : v + 1 = p ^ M := by omega
    rw [hv1, Nat.mod_self, Finset.sum_range_zero, zero_sub, neg_eq_iff_add_eq_zero,
      ← Finset.sum_range_succ, hv1]
    exact hsum

theorem eq_of_shift_invariant (p : ℕ) [Fact p.Prime] {N : Type} (f : ℤ_[p] → N)
    (hf : IsLocallyConstant f) (h : ∀ z, f (z + 1) = f z) (z : ℤ_[p]) : f z = f 0 := by
  have hnat : ∀ k : ℕ, f (k : ℤ_[p]) = f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, h, ih]
  have hcl : IsClosed {x : ℤ_[p] | f x = f 0} := hf.isClosed_fiber (f 0)
  exact PadicInt.denseRange_natCast.induction_on z hcl hnat

end GlobalTheory.CompanionTheory.PadicShift
