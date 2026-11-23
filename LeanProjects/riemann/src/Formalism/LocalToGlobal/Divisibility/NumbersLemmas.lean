import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
import Formalism.LocalRingCardinality.HostCls
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain
open scoped BigOperators

namespace NumDatum

variable (N : NumDatum)

theorem pos_zero (p : ℕ) (z : RPl N.R) : N.pos p z 0 = z := by
  unfold NumDatum.pos
  simp

theorem pos_add (p : ℕ) (z : RPl N.R) (a b : ℕ) : N.pos p (N.pos p z a) b = N.pos p z (a + b) := by
  unfold NumDatum.pos

  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    · refine Prod.ext ?_ ?_
      · by_cases hc : N.cls p = PrimeClass.signal <;>
          cases z.1 <;> simp [hc, Nat.odd_iff, Nat.add_mod, ha, hb]
      · simp only [add_smul, add_assoc]

theorem pos_period (p : ℕ) (z : RPl N.R) : N.pos p z (N.ordP p) = z := by
  unfold NumDatum.pos NumDatum.ordP
  split_ifs with hc
  · have h1 : (2 * addOrderOf (2 • N.hP p)) • N.hP p = 0 := by
      rw [mul_comm, ← smul_smul, addOrderOf_nsmul_eq_zero]
    have h2 : ¬ Odd (2 * addOrderOf (2 • N.hP p)) := Nat.not_odd_iff_even.mpr (even_two_mul _)
    simp [h1, h2]
  · simp [hc, addOrderOf_nsmul_eq_zero]

theorem pos_mul_period (p : ℕ) (z : RPl N.R) (c : ℕ) : N.pos p z (N.ordP p * c) = z := by
  induction c with
  | zero => simpa using N.pos_zero p z
  | succ c ih => rw [Nat.mul_succ, ← N.pos_add, ih, N.pos_period]

theorem pos_mod (p : ℕ) (z : RPl N.R) (e : ℕ) : N.pos p z (e % N.ordP p) = N.pos p z e := by
  conv_rhs => rw [← Nat.div_add_mod e (N.ordP p)]
  rw [← N.pos_add, N.pos_mul_period]

private theorem lpF_comp_add (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (a : ZMod d) :
    lpF l d (fun s => Ds (s + a)) = lpF l d Ds := by
  have hsum : ∑ s, Ds (s + a) = ∑ s, Ds s := Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)
  have hset : lpFeasible l d (fun s => Ds (s + a)) = lpFeasible l d Ds := by
    ext y
    simp only [Formalism.BasicNotions.lpFeasible, Set.mem_setOf_eq]
    constructor
    · rintro ⟨xs, h0, h1, h2, rfl⟩
      refine ⟨fun s i => xs (s - a) i, fun s i => h0 _ _, fun s i h => h1 _ _ h, fun s => ?_, ?_⟩
      · have := h2 (s - a)
        rw [sub_add_cancel] at this
        simpa only [sub_right_comm] using this
      · exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun x => by simp)
    · rintro ⟨xs, h0, h1, h2, rfl⟩
      refine ⟨fun s i => xs (s + a) i, fun s i => h0 _ _, fun s i h => h1 _ _ h, fun s => ?_, ?_⟩
      · have := h2 (s + a)
        simpa only [sub_add_eq_add_sub] using this
      · exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun x => by simp)
  unfold Formalism.BasicNotions.lpF
  rw [hsum, hset]

theorem FOrb_step (j p : ℕ) (z : RPl N.R) (e : ℕ) : N.FOrb j p (N.pos p z e) = N.FOrb j p z := by
  have key : ∀ s : ZMod (N.ordP p),
      N.pos p (N.pos p z e) s.val = N.pos p z (s + (e : ZMod (N.ordP p))).val := by
    intro s
    rw [N.pos_add, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, add_comm s.val e, N.pos_mod]
  unfold NumDatum.FOrb
  simp_rw [key]
  exact lpF_comp_add p (N.ordP p) (fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos p z s.val)) (e : ZMod (N.ordP p))

theorem pos_fix (p : ℕ) (y : RPl N.R) (c : ℕ) (h : N.pos p y c = y) : N.ordP p ∣ c := by
  obtain ⟨b, a⟩ := y
  simp only [NumDatum.pos, Prod.mk.injEq] at h
  have h3 : c • N.hP p = 0 := by simpa using h.2
  unfold NumDatum.ordP
  split_ifs with hc
  · have hodd : ¬ Odd c := by
      intro ho
      cases b <;> simp [hc, ho] at h
    obtain ⟨k, rfl⟩ : Even c := Nat.not_odd_iff_even.mp hodd
    have hk : k • (2 • N.hP p) = 0 := by rw [smul_smul, mul_two]; exact h3
    rw [← two_mul]
    exact Nat.mul_dvd_mul_left 2 (addOrderOf_dvd_of_nsmul_eq_zero hk)
  · exact addOrderOf_dvd_of_nsmul_eq_zero h3

theorem pos_inj (p : ℕ) (z : RPl N.R) (a b : ℕ) (ha : a < N.ordP p) (hb : b < N.ordP p)
    (h : N.pos p z a = N.pos p z b) : a = b := by
  rcases le_total a b with hab | hab
  · have h' : N.pos p (N.pos p z a) (b - a) = N.pos p z a := by
      rw [N.pos_add, show a + (b - a) = b by omega, h]
    have hd := Nat.eq_zero_of_dvd_of_lt (N.pos_fix p _ _ h') (by omega)
    omega
  · have h' : N.pos p (N.pos p z b) (a - b) = N.pos p z b := by
      rw [N.pos_add, show b + (a - b) = a by omega, h]
    have hd := Nat.eq_zero_of_dvd_of_lt (N.pos_fix p _ _ h') (by omega)
    omega

theorem sum_orbits (j p : ℕ) (T : Finset (RPl N.R))
    (hT : ∀ z, ∃! r, r ∈ T ∧ ∃ e : ℕ, N.pos p r e = z) :
    (∑ z : RPl N.R, N.FOrb j p z) / (N.ordP p : ℝ) = ∑ r ∈ T, N.FOrb j p r := by
  have hd : (N.ordP p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  rw [div_eq_iff hd]

  have hsum : ∑ z : RPl N.R, N.FOrb j p z =
      ∑ x ∈ T ×ˢ Finset.range (N.ordP p), N.FOrb j p (N.pos p x.1 x.2) := by
    symm
    apply Finset.sum_bij (fun x _ => N.pos p x.1 x.2)
    · intro x _
      exact Finset.mem_univ _
    · rintro ⟨r, e⟩ hx ⟨r', e'⟩ hx' h
      simp only [Finset.mem_product, Finset.mem_range] at hx hx'
      have hr : r = r' := by
        obtain ⟨r0, _, huniq⟩ := hT (N.pos p r e)
        have h1 := huniq r ⟨hx.1, e, rfl⟩
        have h2 := huniq r' ⟨hx'.1, e', h.symm⟩
        rw [h1, h2]
      subst hr
      rw [N.pos_inj p r e e' hx.2 hx'.2 h]
    · intro z _
      obtain ⟨r, ⟨hr, e, he⟩, _⟩ := hT z
      refine ⟨(r, e % N.ordP p), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range]
        exact ⟨hr, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩
      · show N.pos p r (e % N.ordP p) = z
        rw [N.pos_mod, he]
    · intro x _
      rfl
  rw [hsum, Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  simp only [N.FOrb_step]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

theorem ne_of_inert {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ}
    (h : primeClass H p = PrimeClass.inertClass ∨ primeClass H p = PrimeClass.signal) :
    p ≠ 2 ∧ p ≠ H.q ∧ p ≠ H.d := by
  have h3 : p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d := by
    rcases h with h | h
    · obtain ⟨a, b, c, -⟩ := (primeClass_eq_inert_iff H).1 h
      exact ⟨a, b, c⟩
    · obtain ⟨a, b, c, -⟩ := (primeClass_eq_signal_iff H).1 h
      exact ⟨a, b, c⟩
  exact ⟨fun e => h3.1 (e ▸ H.two_mem_small), h3.2⟩

theorem not_dvd_of_inert {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ} (hp : p.Prime)
    (h : primeClass H p = PrimeClass.inertClass ∨ primeClass H p = PrimeClass.signal) : ¬ p ∣ H.condN :=
  h.elim (not_dvd_conductor_of_inert hp) (not_dvd_of_signal hp)

theorem eq_d_of_ramD {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ} (h : primeClass H p = PrimeClass.ramD) : p = H.d := by
  unfold Formalism.BasicNotions.primeClass at h
  split_ifs at h <;> simp_all

section Cases

variable (j : ℕ) {p : ℕ}

theorem FjP_g (hg : p = N.g 0 ∨ p = N.g 1) : N.FjP j p = N.FTypeG j := by
  unfold NumDatum.FjP
  exact if_pos hg

theorem FjP_d (hg : ¬ (p = N.g 0 ∨ p = N.g 1)) (hd : N.cls p = PrimeClass.ramD) : N.FjP j p = N.FRamD j := by
  unfold NumDatum.FjP
  rw [if_neg hg, if_pos hd]

theorem FjP_inert (hg : ¬ (p = N.g 0 ∨ p = N.g 1)) (hc : N.cls p = PrimeClass.inertClass ∨ N.cls p = PrimeClass.signal)
    (hX : (p : ℝ) ≤ N.sc.X'' N.R.n) : N.FjP j p = N.FInert j p := by
  unfold NumDatum.FjP
  have hd : N.cls p ≠ PrimeClass.ramD := by rcases hc with h | h <;> simp [h]
  rw [if_neg hg, if_neg hd, if_pos ⟨hc, hX⟩]

theorem FjP_split (hg : ¬ (p = N.g 0 ∨ p = N.g 1)) (hc : N.cls p = PrimeClass.splitK ∨ N.cls p = PrimeClass.ram2 ∨
    N.cls p = PrimeClass.ramQ) : N.FjP j p = 0 := by
  unfold NumDatum.FjP
  have hd : N.cls p ≠ PrimeClass.ramD := by rcases hc with h | h | h <;> simp [h]
  have hi : ¬ ((N.cls p = PrimeClass.inertClass ∨ N.cls p = PrimeClass.signal) ∧ (p : ℝ) ≤ N.sc.X'' N.R.n) := by
    rcases hc with h | h | h <;> simp [h]
  rw [if_neg hg, if_neg hd, if_neg hi]

theorem FjP_above (hX : N.sc.X'' N.R.n < (p : ℝ)) (hg : ¬ (p = N.g 0 ∨ p = N.g 1)) (hd : p ≠ N.d) : N.FjP j p = 0 := by
  unfold NumDatum.FjP
  have hr : N.cls p ≠ PrimeClass.ramD := fun h => hd (eq_d_of_ramD h)
  rw [if_neg hg, if_neg hr, if_neg (fun h => absurd h.2 (not_le.mpr hX))]

theorem FjP_off_supp (hp : p.Prime) (hs : p ∉ N.suppP) : N.FjP j p = 0 := by
  unfold NumDatum.suppP at hs
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hfl : ⌊N.sc.X'' N.R.n⌋₊ < p := by
    by_contra hc
    exact h1 ⟨by omega, hp⟩
  exact N.FjP_above j (Nat.lt_of_floor_lt hfl) (fun h => h.elim h2 h3) h4

end Cases

def FjConj : Prop :=
  ∀ (N : NumDatum) (K : Type) [Field K] [NumberField K] [StarRing K] (j : ℕ) (w : HeightOneSpectrum (𝓞 K)),
    N.Fj j (Formalism.DivisionValues.conjPl w) = N.Fj j w

theorem fjConj_of (h : Formalism.EigenvalueLevelCeiling.RamBasic) : FjConj := by
  intro N K _ _ _ j w
  unfold Fj
  rw [(h K w).2.2.1]

theorem nu_eq_originRow (δ : Code N) (j : ℕ) (hj : 1 ≤ j) (z : RPl N.R) (i : ℕ) :
    ((N.nu δ j z i : ℚ) : ℝ) =
      Formalism.DivisionValues.originRow N.R.k N.R.t j (N.w j z) ((N.srcPar δ z i : ℚ) : ℝ) ((i : ℝ) + 1) := by
  unfold NumDatum.nu Formalism.DivisionValues.originRow NumDatum.w Formalism.BasicNotions.Ranks.N
  push_cast [Nat.cast_sub hj]
  ring

theorem aPlus_eq_originBig (j : ℕ) (z : RPl N.R) (i : ℕ) :
    ((N.aPlus j z i : ℚ) : ℝ) =
      Formalism.DivisionValues.originBig N.R.k N.R.m N.R.t j (N.w j z) ((N.sigPar z i : ℚ) : ℝ) ((i : ℝ) + 1) := by
  have hk := N.R.m_add_three_le_k
  have hnV : (N.R.nV : ℚ) = N.R.k + N.R.m - 1 + N.R.t := by
    unfold Formalism.BasicNotions.Ranks.nV Formalism.BasicNotions.Ranks.r
    rw [Nat.cast_add, Nat.cast_sub (show 1 ≤ N.R.k + N.R.m by omega)]
    push_cast
    ring
  unfold NumDatum.aPlus Formalism.DivisionValues.originBig NumDatum.w
  rw [hnV]
  push_cast
  ring

theorem eQ_int (j : ℕ) (z : RPl N.R) : ∃ a : ℤ, N.eQ j z = a := by
  unfold NumDatum.eQ
  split_ifs
  · exact (N.hc z).e_int _
  · exact ⟨0, by simp⟩

theorem sigPar_int (z : RPl N.R) (i : ℕ) : ∃ a : ℤ, N.sigPar z i = a := by
  unfold NumDatum.sigPar
  split_ifs with h hb
  · exact (N.hc z).v_int _
  · obtain ⟨a, ha⟩ := (N.hc z).b_int ⟨i - (N.R.k - 1), hb⟩
    exact ⟨-a, by rw [ha]; push_cast; ring⟩
  · exact ⟨0, by simp⟩

theorem aPlus_int (j : ℕ) (z : RPl N.R) (i : ℕ) : ∃ a : ℤ, N.aPlus j z i = a := by
  obtain ⟨s, hs⟩ := N.R.t_odd
  obtain ⟨a, ha⟩ := N.eQ_int j z
  obtain ⟨x, hx⟩ := N.sigPar_int z i
  have hk := N.R.m_add_three_le_k
  have hnV : (N.R.nV : ℚ) = N.R.k + N.R.m - 1 + N.R.t := by
    unfold Formalism.BasicNotions.Ranks.nV Formalism.BasicNotions.Ranks.r
    rw [Nat.cast_add, Nat.cast_sub (show 1 ≤ N.R.k + N.R.m by omega)]
    push_cast
    ring
  refine ⟨x + a - ((N.R.k : ℤ) + s - 1 + j - i), ?_⟩
  unfold NumDatum.aPlus
  rw [hx, ha, hnV, hs]
  push_cast
  ring

theorem aMinus_int (j : ℕ) (z : RPl N.R) (c : ℕ) : ∃ a : ℤ, N.aMinus j z c = a := by
  obtain ⟨s, hs⟩ := N.R.t_odd
  obtain ⟨a, ha⟩ := N.eQ_int j z
  have hb : ∃ x : ℤ, (if h : j + c < N.R.m then (N.hc z).b ⟨j + c, h⟩ else 0) = x := by
    split_ifs with h
    · exact (N.hc z).b_int _
    · exact ⟨0, by simp⟩
  obtain ⟨x, hx⟩ := hb
  refine ⟨x - a - (s + 1 + c), ?_⟩
  unfold NumDatum.aMinus
  rw [hx, ha, hs]
  push_cast
  ring

theorem uW_half (δ : Code N) (z : RPl N.R) (i : Fin N.R.k) : ∃ a : ℤ, N.uW δ z i = a + 1 / 2 := by
  unfold NumDatum.uW
  split_ifs with h h'
  · obtain ⟨x, hx⟩ := (N.hc z).v_int ⟨i.1 - 1, by omega⟩
    exact ⟨x - 1 - N.Del, by rw [hx]; push_cast; ring⟩
  · obtain ⟨x, hx⟩ := (N.hc z).v_int ⟨i.1 - 1, by omega⟩
    exact ⟨x - 1, by rw [hx]; push_cast; ring⟩
  · exact (N.hc z).u_half i

theorem srcPar_half (δ : Code N) (z : RPl N.R) (i : ℕ) (hi : i < N.Nm) : ∃ a : ℤ, N.srcPar δ z i = a + 1 / 2 := by
  unfold NumDatum.srcPar
  split_ifs with h hb
  · exact N.uW_half δ z ⟨i, h⟩
  · obtain ⟨s, hs⟩ := N.R.t_odd
    have ht : (N.R.t : ℚ) = 2 * s + 1 := by rw [hs]; push_cast; ring
    obtain ⟨x, hx⟩ := (N.hc z).e_int ⟨(i - N.R.k) / (N.R.t + 1), hb⟩
    refine ⟨-x + s - ((i - N.R.k) % (N.R.t + 1) : ℕ), ?_⟩
    rw [hx]
    generalize (i - N.R.k) % (N.R.t + 1) = r
    rw [ht]
    push_cast
    ring
  · exfalso
    apply hb
    unfold NumDatum.Nm Formalism.BasicNotions.Ranks.N at hi
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < N.R.t + 1)]
    omega

theorem nu_int (δ : Code N) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ N.R.m) (z : RPl N.R) (i : ℕ) (hi : i < N.R.N (j - 1)) :
    ∃ a : ℤ, N.nu δ j z i = a := by
  have hNm : i < N.Nm := by
    unfold NumDatum.Nm Formalism.BasicNotions.Ranks.N at *
    have : (j - 1) * (N.R.t + 1) ≤ N.R.m * (N.R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨a, ha⟩ := N.srcPar_half δ z i hNm
  obtain ⟨b, hb⟩ := N.eQ_int j z
  obtain ⟨s, hs⟩ := N.R.t_odd
  have ht : (N.R.t : ℚ) = 2 * s + 1 := by rw [hs]; push_cast; ring
  refine ⟨a + b - ((N.R.k : ℤ) + (2 * (j : ℤ) - 1) * (s + 1)) + i + 1, ?_⟩
  unfold NumDatum.nu Formalism.BasicNotions.Ranks.N
  rw [ha, hb]
  push_cast [Nat.cast_sub h1]
  rw [ht]
  ring

theorem sigPar_step (z : RPl N.R) (i : ℕ) (hi : i + 1 < N.R.k - 1 + N.R.m) :
    N.sigPar z (i + 1) + 1 ≤ N.sigPar z i := by
  have hk := N.R.m_add_three_le_k
  have ht : (0 : ℚ) ≤ N.R.t := Nat.cast_nonneg _
  unfold NumDatum.sigPar
  by_cases h1 : i + 1 < N.R.k - 1
  ·
    have h0 : i < N.R.k - 1 := by omega
    rw [dif_pos h1, dif_pos h0]
    have a1 : (N.hc z).v ⟨i + 1, h1⟩ < (N.hc z).u ⟨i + 1, by omega⟩ := (N.hc z).u_gt_v ⟨i + 1, h1⟩
    have a2 : (N.hc z).u ⟨i + 1, by omega⟩ < (N.hc z).v ⟨i, h0⟩ := (N.hc z).v_gt_u ⟨i, h0⟩
    obtain ⟨x, hx⟩ := (N.hc z).v_int ⟨i + 1, h1⟩
    obtain ⟨y, hy⟩ := (N.hc z).v_int ⟨i, h0⟩
    rw [hx] at a1 ⊢
    rw [hy] at a2 ⊢
    have hxy : x < y := by exact_mod_cast a1.trans a2
    have := Int.add_one_le_iff.mpr hxy
    exact_mod_cast this
  · by_cases h0 : i < N.R.k - 1
    ·
      rw [dif_neg h1, dif_pos h0, dif_pos (show i + 1 - (N.R.k - 1) < N.R.m by omega)]
      have hb0 : (N.hc z).b ⟨i + 1 - (N.R.k - 1), by omega⟩ = (N.hc z).b ⟨0, by omega⟩ :=
        congrArg (N.hc z).b (Fin.ext (show i + 1 - (N.R.k - 1) = 0 by omega))
      have a1 : -(N.hc z).b ⟨0, by omega⟩ < (N.hc z).u ⟨N.R.k - 1, by omega⟩ :=
        (N.hc z).u_last_gt (by omega) (by omega)
      have hu : (N.hc z).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).u ⟨i + 1, by omega⟩ :=
        congrArg (N.hc z).u (Fin.ext (show N.R.k - 1 = i + 1 by omega))
      have a2 : (N.hc z).u ⟨i + 1, by omega⟩ < (N.hc z).v ⟨i, h0⟩ := (N.hc z).v_gt_u ⟨i, h0⟩
      obtain ⟨x, hx⟩ := (N.hc z).b_int ⟨0, by omega⟩
      obtain ⟨y, hy⟩ := (N.hc z).v_int ⟨i, h0⟩
      rw [hu, hx] at a1
      rw [hy] at a2
      rw [hb0, hx, hy]
      have hxy : -x < y := by exact_mod_cast a1.trans a2
      have := Int.add_one_le_iff.mpr hxy
      push_cast
      exact_mod_cast this
    ·
      have hl : i - (N.R.k - 1) < N.R.m := by omega
      rw [dif_neg h1, dif_neg h0, dif_pos (show i + 1 - (N.R.k - 1) < N.R.m by omega), dif_pos hl]
      have g1 := (N.hc z).gap_be ⟨i - (N.R.k - 1), hl⟩
      have g2 : ((N.R.t : ℚ) + 3) / 2 ≤ (N.hc z).b ⟨i - (N.R.k - 1) + 1, by omega⟩ -
          (N.hc z).e ⟨i - (N.R.k - 1), hl⟩ :=
        (N.hc z).gap_eb ⟨i - (N.R.k - 1), hl⟩ (by show i - (N.R.k - 1) + 1 < N.R.m; omega)
      have hb : (N.hc z).b ⟨i - (N.R.k - 1) + 1, by omega⟩ = (N.hc z).b ⟨i + 1 - (N.R.k - 1), by omega⟩ :=
        congrArg (N.hc z).b (Fin.ext (show i - (N.R.k - 1) + 1 = i + 1 - (N.R.k - 1) by omega))
      rw [hb] at g2
      linarith

theorem sigW_fst (j : ℕ) : (N.R.sigW j).1 = N.R.k + j - 1 := rfl
theorem sigW_snd (j : ℕ) : (N.R.sigW j).2 = N.R.m - j := rfl

theorem aPlus_step (j : ℕ) (h2 : j ≤ N.R.m) (z : RPl N.R) (i : ℕ) (hi : i + 1 < (N.R.sigW j).1) :
    N.aPlus j z (i + 1) ≤ N.aPlus j z i := by
  have hs := N.sigPar_step z i (by rw [N.sigW_fst] at hi; omega)
  unfold NumDatum.aPlus
  push_cast
  linarith

theorem aPlus_last (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ N.R.m) (z : RPl N.R) :
    1 ≤ N.aPlus j z ((N.R.sigW j).1 - 1) := by
  have hk := N.R.m_add_three_le_k
  have hi : (N.R.sigW j).1 - 1 = N.R.k - 1 + (j - 1) := by rw [N.sigW_fst]; omega
  have hnV : (N.R.nV : ℚ) = N.R.k + N.R.m - 1 + N.R.t := by
    unfold Formalism.BasicNotions.Ranks.nV Formalism.BasicNotions.Ranks.r
    rw [Nat.cast_add, Nat.cast_sub (show 1 ≤ N.R.k + N.R.m by omega)]
    push_cast
    ring
  have hic : ((N.R.k - 1 + (j - 1) : ℕ) : ℚ) = N.R.k + j - 2 := by
    rw [Nat.cast_add, Nat.cast_sub (show 1 ≤ N.R.k by omega), Nat.cast_sub h1]
    push_cast
    ring
  have hjm : j - 1 < N.R.m := by omega
  have hs : N.sigPar z (N.R.k - 1 + (j - 1)) = -(N.hc z).b ⟨j - 1, hjm⟩ := by
    unfold NumDatum.sigPar
    rw [dif_neg (show ¬ (N.R.k - 1 + (j - 1) < N.R.k - 1) by omega),
      dif_pos (show N.R.k - 1 + (j - 1) - (N.R.k - 1) < N.R.m by omega)]
    exact congrArg (fun x => -(N.hc z).b x) (Fin.ext (show N.R.k - 1 + (j - 1) - (N.R.k - 1) = j - 1 by omega))
  have he : N.eQ j z = (N.hc z).e ⟨j - 1, hjm⟩ := by
    unfold NumDatum.eQ
    rw [dif_pos ⟨h1, h2⟩]
  have g := (N.hc z).gap_be ⟨j - 1, hjm⟩
  unfold NumDatum.aPlus
  rw [hi, hs, he, hnV, hic]
  linarith

theorem aPlus_ge_one (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ N.R.m) (z : RPl N.R) (i : ℕ) (hi : i < (N.R.sigW j).1) :
    1 ≤ N.aPlus j z i := by
  obtain ⟨d, hd⟩ : ∃ d, i + d = (N.R.sigW j).1 - 1 := ⟨_, Nat.add_sub_of_le (by omega)⟩
  induction d generalizing i with
  | zero =>
    simp only [Nat.add_zero] at hd
    rw [hd]
    exact N.aPlus_last j h1 h2 z
  | succ d ih =>
    exact le_trans (ih (i + 1) (by omega) (by omega)) (N.aPlus_step j h2 z i (by omega))

theorem aMinus_step (j : ℕ) (z : RPl N.R) (c : ℕ) (hc : c + 1 < (N.R.sigW j).2) :
    N.aMinus j z c ≤ N.aMinus j z (c + 1) := by
  have hm : j + (c + 1) < N.R.m := by rw [N.sigW_snd] at hc; omega
  have hm' : j + c < N.R.m := by omega
  have ht : (0 : ℚ) ≤ N.R.t := Nat.cast_nonneg _
  unfold NumDatum.aMinus
  rw [dif_pos hm, dif_pos hm']
  have g1 := (N.hc z).gap_be ⟨j + c, hm'⟩
  have g2 : ((N.R.t : ℚ) + 3) / 2 ≤ (N.hc z).b ⟨j + (c + 1), hm⟩ - (N.hc z).e ⟨j + c, hm'⟩ :=
    (N.hc z).gap_eb ⟨j + c, hm'⟩ (by show j + c + 1 < N.R.m; omega)
  push_cast
  linarith

theorem aMinus_zero (j : ℕ) (h1 : 1 ≤ j) (z : RPl N.R) (hq : 0 < (N.R.sigW j).2) : 1 ≤ N.aMinus j z 0 := by
  have hjm : j < N.R.m := by rw [N.sigW_snd] at hq; omega
  have hm' : j + 0 < N.R.m := by omega
  have he : N.eQ j z = (N.hc z).e ⟨j - 1, by omega⟩ := by
    unfold NumDatum.eQ
    rw [dif_pos ⟨h1, hjm.le⟩]
  have g : ((N.R.t : ℚ) + 3) / 2 ≤ (N.hc z).b ⟨j - 1 + 1, by omega⟩ - (N.hc z).e ⟨j - 1, by omega⟩ :=
    (N.hc z).gap_eb ⟨j - 1, by omega⟩ (by show j - 1 + 1 < N.R.m; omega)
  have hb : (N.hc z).b ⟨j - 1 + 1, by omega⟩ = (N.hc z).b ⟨j + 0, hm'⟩ :=
    congrArg (N.hc z).b (Fin.ext (show j - 1 + 1 = j + 0 by omega))
  rw [hb] at g
  unfold NumDatum.aMinus
  rw [dif_pos hm', he]
  push_cast
  linarith

theorem aMinus_ge_one (j : ℕ) (h1 : 1 ≤ j) (z : RPl N.R) (c : ℕ) (hc : c < (N.R.sigW j).2) : 1 ≤ N.aMinus j z c := by
  induction c with
  | zero => exact N.aMinus_zero j h1 z (by omega)
  | succ c ih => exact le_trans (ih (by omega)) (N.aMinus_step j z c hc)

def RowsArePartitions : Prop :=
  ∀ (N : NumDatum) (j : ℕ), 1 ≤ j → j ≤ N.R.m → ∀ z : RPl N.R,
    (∀ i, i + 1 < (N.R.sigW j).1 → N.aPlus j z (i + 1) ≤ N.aPlus j z i) ∧
    1 ≤ N.aPlus j z ((N.R.sigW j).1 - 1) ∧
    (∀ c, c + 1 < (N.R.sigW j).2 → N.aMinus j z c ≤ N.aMinus j z (c + 1)) ∧
    (0 < (N.R.sigW j).2 → 1 ≤ N.aMinus j z 0)

theorem rowsArePartitions : RowsArePartitions :=
  fun N j h1 h2 z => ⟨fun i hi => N.aPlus_step j h2 z i hi, N.aPlus_last j h1 h2 z,
    fun c hc => N.aMinus_step j z c hc, fun hq => N.aMinus_zero j h1 z hq⟩

def ChiKIsKronecker : Prop :=
  ∀ N : NumDatum, (∀ n : ℕ, Odd n → N.chiK (n : ZMod N.d) = ((jacobiSym (-(N.d : ℤ)) n : ℤ) : ℂ)) ∧
    N.chiK (2 : ZMod N.d) = 1

theorem chiKIsKronecker : ChiKIsKronecker := by
  intro N
  have : Fact N.d.Prime := ⟨N.hyp.2.1⟩
  have hd16 := N.hyp.2.2.2.1
  have hd4 : N.d % 4 = 3 := by omega
  have hdodd : Odd N.d := Nat.odd_iff.2 (by omega)
  constructor
  · intro n hn
    have h1 : N.chiK (n : ZMod N.d) = ((legendreSym N.d n : ℤ) : ℂ) := by
      unfold chiK legendreSym
      simp [MulChar.ringHomComp_apply]
    rw [h1]
    congr 1
    rw [jacobiSym.legendreSym.to_jacobiSym, neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hn]
    rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hn) with h | h
    · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hdodd]
    · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd4 h]; ring
  · have h2 : IsSquare (2 : ZMod N.d) := (ZMod.exists_sq_eq_two_iff (by omega)).2 (Or.inr (by omega))
    have hne : (2 : ZMod N.d) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod N.d) = 0 := by exact_mod_cast h
      have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 N.d).1 h')
      omega
    unfold chiK
    rw [MulChar.ringHomComp_apply, (quadraticChar_one_iff_isSquare hne).2 h2]
    simp

def FoPlaces : Prop :=
  ∀ (N : NumDatum) (K : Type) [Field K] [NumberField K],
    (∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      Formalism.DivisionValues.lw w * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * N.Fj j w)).Finite) ∧
    ∑ j ∈ N.lifts, ∑ᶠ w : HeightOneSpectrum (𝓞 K), Formalism.DivisionValues.lw w * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * N.Fj j w) = N.Fo

def FInertGe : Prop :=
  ∀ (N : NumDatum) (j p : ℕ), p.Prime → (N.cls p = PrimeClass.inertClass ∨ N.cls p = PrimeClass.signal) →
    (∀ z, 0 ≤ N.w j z) →
    ∑ z : RPl N.R, ((N.R.k : ℝ) - 1) * N.w j z / ((p : ℝ) ^ 2 - 1) ≤ N.FInert j p

def FInertFlat : Prop :=
  ∀ (N : NumDatum) (j p : ℕ), p.Prime → (N.cls p = PrimeClass.inertClass ∨ N.cls p = PrimeClass.signal) →
    (∀ z, 0 ≤ N.w j z) → (∀ z z', N.w j z' ≤ (p : ℝ) * N.w j z) →
    N.FInert j p = ∑ z : RPl N.R, ((N.R.k : ℝ) - 1) * N.w j z / ((p : ℝ) ^ 2 - 1)

def HookLower : Prop :=
  ∀ (N : NumDatum) (j : ℕ), 1 ≤ j → j ≤ N.R.m → ∀ z : RPl N.R,
    Formalism.DivisionValues.logFactRows (N.apRows j z) ≤ N.logHook j z

theorem apDiag_rowLens (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ N.R.m) (z : RPl N.R) :
    ((N.apDiag j z).rowLens : Multiset ℕ) = N.apRows j z := by
  have hpos : ∀ x ∈ ((List.range (N.R.sigW j).1).map (N.apN j z)).insertionSort (· ≥ ·), 0 < x := by
    intro x hx
    rw [(List.perm_insertionSort _ _).mem_iff, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    unfold apN
    rw [Int.lt_toNat]
    have h3 := N.aPlus_ge_one j h1 h2 z i hi
    have h4 : (1 : ℤ) ≤ ⌊N.aPlus j z i⌋ := Int.le_floor.2 (by exact_mod_cast h3)
    push_cast
    omega
  unfold apDiag apRows
  rw [YoungDiagram.rowLens_ofRowLens_eq_self hpos]
  exact Multiset.coe_eq_coe.2 (List.perm_insertionSort _ _)

theorem hookLower_of (h : Formalism.DivisionValues.RowsHook) : HookLower := by
  intro N j h1 h2 z
  have := h (N.apDiag j z)
  rw [N.apDiag_rowLens j h1 h2 z] at this
  exact this

end NumDatum

theorem hFrob_five (e : ℕ) : hFrob e 5 = 1 := by
  have hc : Nat.Coprime 5 (2 ^ (e + 2)) := Nat.Coprime.pow_right _ (by norm_num)
  unfold hFrob
  rw [dif_pos hc]
  have hu : ZMod.unitOfCoprime 5 hc = Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2) := rfl
  rw [hu, ← iotaH_one, iotaHInv_iotaH]

def HFrobMul : Prop := ∀ (e a b : ℕ), Odd a → Odd b → hFrob e (a * b) = hFrob e a + hFrob e b

theorem iotaH_iotaHInv (e : ℕ) (x : HGrp e) : iotaH e (iotaHInv e x) = x := Formalism.BasicNotions.iotaH_iotaHInv e x

theorem coprime_of_odd (e : ℕ) {a : ℕ} (ha : Odd a) : Nat.Coprime a (2 ^ (e + 2)) :=
  Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ha.not_two_dvd_nat))

theorem hFrobMul : HFrobMul := by
  intro e a b ha hb
  have hca := coprime_of_odd e ha
  have hcb := coprime_of_odd e hb
  have hcab := coprime_of_odd e (ha.mul hb)
  unfold hFrob
  rw [dif_pos hcab, dif_pos hca, dif_pos hcb]
  have hu : ZMod.unitOfCoprime (a * b) hcab = ZMod.unitOfCoprime a hca * ZMod.unitOfCoprime b hcb := by
    ext
    simp
  apply (iotaH_bijective e).1
  rw [iotaH_add, iotaH_iotaHInv, iotaH_iotaHInv, iotaH_iotaHInv, hu]
  rfl

def HFrobZero : Prop :=
  ∀ (e p : ℕ), Odd p → (hFrob e p = 0 ↔ (p : ZMod (2 ^ (e + 2))) = 1 ∨ (p : ZMod (2 ^ (e + 2))) = -1)

theorem hFrobZero : HFrobZero := by
  intro e p hp
  have cp := coprime_of_odd e hp
  have h0 : iotaH e 0 = 1 := by unfold iotaH; simp
  unfold hFrob
  rw [dif_pos cp]
  constructor
  · intro h
    have h1 : hcl e (ZMod.unitOfCoprime p cp) = hcl e 1 := by
      rw [← iotaH_iotaHInv e (hcl e (ZMod.unitOfCoprime p cp)), h, h0, hcl_one]
    rcases (hcl_eq_hcl_iff _ _).1 h1 with h2 | h2
    · left
      have := congrArg (fun u : (ZMod (2 ^ (e + 2)))ˣ => (u : ZMod (2 ^ (e + 2)))) h2
      simpa [ZMod.coe_unitOfCoprime] using this
    · right
      have := congrArg (fun u : (ZMod (2 ^ (e + 2)))ˣ => (u : ZMod (2 ^ (e + 2)))) h2
      simpa [ZMod.coe_unitOfCoprime] using this
  · intro h
    have h1 : hcl e (ZMod.unitOfCoprime p cp) = hcl e 1 := by
      refine (hcl_eq_hcl_iff _ _).2 ?_
      rcases h with h | h
      · exact Or.inl (Units.ext (by rw [ZMod.coe_unitOfCoprime, h]; rfl))
      · exact Or.inr (Units.ext (by rw [ZMod.coe_unitOfCoprime, h]; simp))
    apply (factIota e).1.1
    rw [iotaH_iotaHInv, h1, h0, hcl_one]

open Formalism.MainNotions.G

abbrev ofRecord (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) : NumDatum where
  R := D.R
  sc := L.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := Del
  h0 := h0
  hc := fun z => D.hc (tauPl D z)

section Record

variable (D : D7) (L : SizeData₂ D) (Del h0 : ℕ)

abbrev letterOf (u : D.what₂.Word) : Code (ofRecord D L Del h0) := D.s.letter u

theorem tauPl_bijective : Function.Bijective (tauPl D) := by
  have hI := D.R.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨β, t⟩ ⟨β', t'⟩ h
    have h1 : plGG D (β, t) = plGG D (β', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases β <;> cases β'
    · have h2 : D.R.tau1 t = D.R.tau1 t' := h1
      rw [hI (Prod.ext_iff.1 h2).2]
    · exact absurd (show D.R.tau1 t = D.R.tau2 t' from h1) (hP.2 t t')
    · exact absurd (show D.R.tau1 t' = D.R.tau2 t from h1.symm) (hP.2 t' t)
    · have h2 : D.R.tau2 t = D.R.tau2 t' := h1
      rw [hI (Prod.ext_iff.1 h2).2]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨(false, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩
    · exact ⟨(true, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩

theorem hP_eq_art {p : ℕ} (hp : p.Prime) (hc : Nat.Coprime p D.host.condN) :
    Formalism.MainNotions.G.hP D p = D.R.iotaInv (D.host.art (ZMod.unitOfCoprime p hc)).2 := by
  have := Fact.mk hp
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨P, hP1, hP2⟩ := Ideal.nonempty_primesOver (P := Ideal.span {(p : ℤ)}) (S := 𝓞 D.host.E)
  have hne : ∃ g, g ∈ frobSet D p := by
    obtain ⟨σ, hσ⟩ := (D.host.der.frob p (hp.coprime_iff_not_dvd.1 hc) P).1
    exact ⟨_, P, hP1, hP2, σ, hσ, rfl⟩
  obtain ⟨P', i1, i2, σ, hσ, hg⟩ := Classical.epsilon_spec hne
  have h3 := (D.host.toHostAx.frob_iff p hc P' σ).1 hσ
  unfold Formalism.MainNotions.G.hP
  rw [← hg, h3]

theorem hP_eq_ofRecord {p : ℕ} (hp : p.Prime) (hN : ¬ p ∣ D.host.condN) :
    Formalism.MainNotions.G.hP D p = (ofRecord D L Del h0).hP p := by
  have hc : Nat.Coprime p D.host.condN := hp.coprime_iff_not_dvd.2 hN
  rw [hP_eq_art D hp hc]
  unfold NumDatum.hP
  rw [dif_pos hc]

theorem hP_eq_hFrob {p : ℕ} (hp : p.Prime) (hN : ¬ p ∣ D.host.condN) :
    iotaHInv D.R.e (D.R.hH (D.R.iota (Formalism.MainNotions.G.hP D p))) = hFrob D.R.e p := by
  have hc : Nat.Coprime p D.host.condN := hp.coprime_iff_not_dvd.2 hN
  have hd : 2 ^ (D.R.e + 2) ∣ D.host.condN := (D.host.tower_dvd.mul_right _).mul_right _
  have hc2 : Nat.Coprime p (2 ^ (D.R.e + 2)) := hc.coprime_dvd_right hd
  have h1 := D.host.art_h (ZMod.unitOfCoprime p hc) (ZMod.unitOfCoprime p hc2) (by
    rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.mod_modEq _ _).of_dvd hd).symm)
  unfold hFrob
  rw [dif_pos hc2, hP_eq_art D hp hc, Formalism.HC.Frame.iota_iotaInv, h1]

theorem ofRecord_cls (p : ℕ) : (ofRecord D L Del h0).cls p = D.host.cls p := rfl

theorem ofRecord_w {j : ℕ} (hj : 1 ≤ j) (z : Bool × HH D) : (ofRecord D L Del h0).w j z = wPl D j z := by
  unfold NumDatum.w NumDatum.eQ wPl wj
  by_cases h : j ≤ D.R.m
  · rw [dif_pos (show 1 ≤ j ∧ j ≤ (ofRecord D L Del h0).R.m from ⟨hj, h⟩), dif_pos (show j - 1 < D.R.m by omega)]
  · rw [dif_neg (show ¬ (1 ≤ j ∧ j ≤ (ofRecord D L Del h0).R.m) from fun h' => h h'.2),
      dif_neg (show ¬ (j - 1 < D.R.m) by omega)]
    simp

variable {p : ℕ} (hh : Formalism.MainNotions.G.hP D p = (ofRecord D L Del h0).hP p)

include hh in
theorem ofRecord_pos (z : Bool × HH D) (s : ℕ) : (ofRecord D L Del h0).pos p z s = posPl D p z s := by
  unfold NumDatum.pos posPl partner
  rw [hh]
  rfl

include hh in
theorem ofRecord_ordP : (ofRecord D L Del h0).ordP p = nP D p := by
  unfold NumDatum.ordP nP
  rw [hh]
  rfl

theorem lpF_congr {l d d' : ℕ} [NeZero d] [NeZero d'] (h : d = d') (f : ℕ → ℝ) :
    lpF l d (fun s => f s.val) = lpF l d' (fun s => f s.val) := by
  subst h
  rfl

include hh in
theorem ofRecord_FOrb {j : ℕ} (hj : 1 ≤ j) (z : Bool × HH D) : (ofRecord D L Del h0).FOrb j p z = FOrb D j p z := by
  unfold NumDatum.FOrb Formalism.BasicNotions.FOrb
  simp only [ofRecord_pos D L Del h0 hh, ofRecord_w D L Del h0 hj]
  exact lpF_congr (ofRecord_ordP D L Del h0 hh) (fun s => ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s))

include hh in
theorem ofRecord_FInert {j : ℕ} (hj : 1 ≤ j) : (ofRecord D L Del h0).FInert j p = FInert D j p := by
  unfold NumDatum.FInert Formalism.BasicNotions.FInert
  have hc : ((ofRecord D L Del h0).cls p = PrimeClass.inertClass ∧ (ofRecord D L Del h0).hP p = 0) ↔
      (IsResidueClassZero D p ∧ Formalism.MainNotions.G.hP D p = 0) := by
    rw [hh]; exact Iff.rfl
  by_cases h : IsResidueClassZero D p ∧ Formalism.MainNotions.G.hP D p = 0
  · rw [if_pos (hc.2 h), if_pos h]
    have e1 : ∀ z : Bool × HH D, ((D.R.k : ℝ) - 1) * (ofRecord D L Del h0).w j z / ((p : ℝ) ^ 2 - 1) =
        ((D.R.k : ℝ) - 1) * wj D j (tauPl D z) / ((p : ℝ) ^ 2 - 1) := fun z => by
      rw [ofRecord_w D L Del h0 hj]; rfl
    exact (Finset.sum_congr rfl (fun z _ => e1 z)).trans
      ((tauPl_bijective D).sum_comp (fun τ => ((D.R.k : ℝ) - 1) * wj D j τ / ((p : ℝ) ^ 2 - 1)))
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h, ofRecord_ordP D L Del h0 hh]
    exact congrArg (· / (nP D p : ℝ))
      (Finset.sum_congr rfl (fun z _ => ofRecord_FOrb D L Del h0 hh hj z))

omit hh

theorem ofRecord_FRamD {j : ℕ} (hj : 1 ≤ j) : (ofRecord D L Del h0).FRamD j = FRamD D j := by
  unfold NumDatum.FRamD Formalism.BasicNotions.FRamD
  exact congrArg (fun s => -(((D.R.k : ℝ) - 1) / 2) * s) (Finset.sum_congr rfl (fun t _ =>
    congrArg₂ min (ofRecord_w D L Del h0 hj (false, t)) (ofRecord_w D L Del h0 hj (true, t))))

def FockDegTie : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), DV.KapDef D → ∀ j, 1 ≤ j → j ≤ D.R.m →
    ((fockDeg D j : ℤ) : ℚ) = (ofRecord D L Del h0).Dplus j + (ofRecord D L Del h0).Dminus j

theorem fockDegTie : FockDegTie := by
  intro D L Del h0 hK j h1 h2
  set N := ofRecord D L Del h0 with hN
  unfold fockDeg NumDatum.Dplus NumDatum.Dminus
  rw [← Finset.sum_add_distrib]
  push_cast
  rw [← (tauPl_bijective D).sum_comp (fun τ => (∑ a, |((D.what₂.kaBig j τ a : ℤ) : ℚ)|) + ∑ a, |((D.what₂.kaSmall j τ a : ℤ) : ℚ)|)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  obtain ⟨hb, hs⟩ := hK j h1 h2 (tauPl D z)
  congr 1
  · rw [Finset.sum_range (fun i => N.aPlus j z i)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hb a]
    exact abs_of_nonneg (le_trans zero_le_one (N.aPlus_ge_one j h1 h2 z a a.2))
  · rw [Finset.sum_range (fun c => N.aMinus j z c)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hs a, abs_neg]
    exact abs_of_nonneg (le_trans zero_le_one (N.aMinus_ge_one j h1 z a a.2))

theorem ofRecord_FTypeG (hK : DV.KapDef D) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (ofRecord D L Del h0).FTypeG j = FTypeG D j := by
  unfold NumDatum.FTypeG FTypeG
  rw [← fockDegTie D L Del h0 hK j h1 h2]
  push_cast
  rfl

theorem ofRecord_FjP {j : ℕ} (hj : 1 ≤ j) {p : ℕ} (hp : p.Prime)
    (hG : (ofRecord D L Del h0).FTypeG j = FTypeG D j) : (ofRecord D L Del h0).FjP j p = FvalP L j p := by
  unfold NumDatum.FjP FvalP
  have hg : (p = (ofRecord D L Del h0).g 0 ∨ p = (ofRecord D L Del h0).g 1) ↔ p ∈ L.gTypes := by
    unfold SizeData₂.gTypes
    rw [Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : p ∈ L.gTypes
  · rw [if_pos (hg.2 h1), if_pos h1, hG]
  · rw [if_neg (fun h => h1 (hg.1 h)), if_neg h1]
    by_cases h2 : D.host.cls p = PrimeClass.ramD
    · rw [if_pos (show (ofRecord D L Del h0).cls p = PrimeClass.ramD from h2), if_pos h2, ofRecord_FRamD D L Del h0 hj]
    · rw [if_neg (show ¬ (ofRecord D L Del h0).cls p = PrimeClass.ramD from h2), if_neg h2]
      by_cases h3 : (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n
      · rw [if_pos (show ((ofRecord D L Del h0).cls p = PrimeClass.inertClass ∨ (ofRecord D L Del h0).cls p = PrimeClass.signal) ∧
          (p : ℝ) ≤ (ofRecord D L Del h0).sc.X'' (ofRecord D L Del h0).R.n from h3), if_pos h3,
          ofRecord_FInert D L Del h0 (hP_eq_ofRecord D L Del h0 hp (NumDatum.not_dvd_of_inert hp h3.1)) hj]
      · rw [if_neg (show ¬ (((ofRecord D L Del h0).cls p = PrimeClass.inertClass ∨
          (ofRecord D L Del h0).cls p = PrimeClass.signal) ∧
          (p : ℝ) ≤ (ofRecord D L Del h0).sc.X'' (ofRecord D L Del h0).R.n) from h3), if_neg h3]

theorem ofRecord_Fval (hK : DV.KapDef D) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : D.what₂.places.Pl) :
    Fval L j w = (ofRecord D L Del h0).FjP j (D.what₂.places.resChar w) :=
  (ofRecord_FjP D L Del h0 h1 (D.what₂.places.resChar_prime w) (ofRecord_FTypeG D L Del h0 hK h1 h2)).symm

theorem ofRecord_rd : (ofRecord D L Del h0).rd = D.host.rdE := rfl

theorem ofRecord_logOm : (ofRecord D L Del h0).logOm = L.logOm := by
  unfold NumDatum.logOm SizeData₂.logOm NumDatum.v Host.v
  rw [ofRecord_rd, L.logDerivative_at_one_eq]
  rfl

theorem ofRecord_La : (ofRecord D L Del h0).La = L.La := by
  unfold NumDatum.La SizeData₂.La
  rw [ofRecord_rd]

theorem ofRecord_uW (hDel : D.s.Del = (Del : ℚ)) (u : D.what₂.Word) (z : Bool × HH D) (i : Fin D.R.k) :
    (ofRecord D L Del h0).uW (letterOf D L Del h0 u) z i = (D.hcW u (tauPl D z)).u i := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  unfold NumDatum.uW
  by_cases h : 1 ≤ i.1 ∧ i.1 + 1 < D.R.k
  · rw [dif_pos (show 1 ≤ i.1 ∧ i.1 + 1 < (ofRecord D L Del h0).R.k from h)]
    have key := D.s.u_letter u (tauPl D z) (i.1 - 1) (by omega)
    have hi : (⟨i.1 - 1 + 1, by omega⟩ : Fin D.R.k) = i := Fin.ext (by show i.1 - 1 + 1 = i.1; omega)
    rw [hi] at key
    rw [key, D.hcW_v, hDel]
  · rw [dif_neg (show ¬ (1 ≤ i.1 ∧ i.1 + 1 < (ofRecord D L Del h0).R.k) from h)]
    have hi : i.1 = 0 ∨ i.1 = D.R.k - 1 := by have := i.2; omega
    rcases hi with hi | hi
    · have e : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [e]
      exact (D.hcW_first u _ (by omega)).symm
    · have e : i = ⟨D.R.k - 1, by omega⟩ := Fin.ext hi
      rw [e]
      exact (D.hcW_last u _ (by omega)).symm

theorem ofRecord_nu (hDel : D.s.Del = (Del : ℚ)) (u : D.what₂.Word) (j : ℕ) (z : Bool × HH D) (i : ℕ) :
    (((ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i : ℚ) : ℝ) = DV.nuRow D u j (tauPl D z) i := by
  have hs : (ofRecord D L Del h0).srcPar (letterOf D L Del h0 u) z i = DV.srcPar D u (tauPl D z) i := by
    unfold NumDatum.srcPar DV.srcPar
    by_cases h : i < D.R.k
    · rw [dif_pos (show i < (ofRecord D L Del h0).R.k from h), dif_pos h]
      exact ofRecord_uW D L Del h0 hDel u z ⟨i, h⟩
    · rw [dif_neg (show ¬ i < (ofRecord D L Del h0).R.k from h), dif_neg h, D.hcW_e]
  have he : (((ofRecord D L Del h0).eQ j z : ℚ) : ℝ) = DV.wSz D j (tauPl D z) := by
    unfold NumDatum.eQ DV.wSz
    by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · rw [dif_pos (show 1 ≤ j ∧ j ≤ (ofRecord D L Del h0).R.m from h), dif_pos h]
    · rw [dif_neg (show ¬ (1 ≤ j ∧ j ≤ (ofRecord D L Del h0).R.m) from h), dif_neg h]
      simp
  unfold NumDatum.nu DV.nuRow
  rw [← he, ← hs]
  push_cast
  rfl

theorem ofRecord_aT (t : D.host.TT) : (((ofRecord D L Del h0).aT t.1 : ℚ) : ℝ) = (L.aT t : ℝ) := by
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have h := (L.top_u (tauPl D (false, (t : D.R.A))) t hk
    (by unfold tauPl; rw [Equiv.apply_symm_apply]; rfl)).1
  have h' : ((((ofRecord D L Del h0).hc (false, (t : D.R.A))).u ⟨0, hk⟩ : ℚ) : ℝ) =
      L.aT t + ((D.R.k : ℝ) - 1) / 2 := h
  unfold NumDatum.aT
  push_cast
  rw [h']
  show (L.aT t : ℝ) + ((D.R.k : ℝ) - 1) / 2 - ((D.R.k : ℝ) - 1) / 2 = L.aT t
  ring

theorem ofRecord_mainT (u : D.what₂.Word) : (ofRecord D L Del h0).mainT (D.mem u).A.T = L.MAIN u := by
  unfold NumDatum.mainT SizeData₂.MAIN
  rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [ofRecord_aT D L Del h0 t, ofRecord_logOm]
  rfl

theorem ofRecord_kerPlace (hDel : D.s.Del = (Del : ℚ)) (u : D.what₂.Word) (j : ℕ) (z : Bool × HH D) :
    (ofRecord D L Del h0).kerPlace (letterOf D L Del h0 u) j z = DV.kerPlace D L u j (tauPl D z) := by
  have e := ofRecord_nu D L Del h0 hDel u j z
  have s1 : ∑ i ∈ Finset.range (D.R.N (j - 1)),
      Formalism.LatticeIndexTer.ph (((ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i : ℚ) : ℝ) =
      ∑ i ∈ Finset.range (D.R.N (j - 1)), phF (DV.nuRow D u j (tauPl D z) i) :=
    Finset.sum_congr rfl (fun i _ => by rw [e i]; rfl)
  have s2 : (((ofRecord D L Del h0).nuAbs (letterOf D L Del h0 u) j z : ℚ) : ℝ) =
      ∑ i ∈ Finset.range (D.R.N (j - 1)), DV.nuRow D u j (tauPl D z) i := by
    unfold NumDatum.nuAbs
    rw [Rat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => e i)
  unfold NumDatum.kerPlace DV.kerPlace
  rw [s2, ofRecord_logOm]
  exact congrArg (fun s => s - (∑ i ∈ Finset.range (D.R.N (j - 1)), DV.nuRow D u j (tauPl D z) i) * L.logOm) s1

theorem ofRecord_hB (hDel : D.s.Del = (Del : ℚ)) (C : ℝ) (u : D.what₂.Word) (j : ℕ) :
    DV.SZbK D L C u j = (ofRecord D L Del h0).hB C (letterOf D L Del h0 u) j +
      C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * (D.host.d : ℝ) ^ C := by
  have s : (∑ z : Bool × HH D, (ofRecord D L Del h0).kerPlace (letterOf D L Del h0 u) j z) =
      ∑ ρ : D.what₂.Tau, DV.kerPlace D L u j ρ :=
    (Finset.sum_congr rfl (fun z _ => ofRecord_kerPlace D L Del h0 hDel u j z)).trans
      ((tauPl_bijective D).sum_comp (fun ρ => DV.kerPlace D L u j ρ))
  have e : (ofRecord D L Del h0).hB C (letterOf D L Del h0 u) j =
      (∑ z : Bool × HH D, (ofRecord D L Del h0).kerPlace (letterOf D L Del h0 u) j z) +
        C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * (ofRecord D L Del h0).La +
        C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L := rfl
  rw [e, s, ofRecord_La]
  unfold DV.SZbK
  ring

theorem ofRecord_hA (hDel : D.s.Del = (Del : ℚ)) (hEta : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) (C : ℝ) (u : D.what₂.Word) :
    DV.SZbP D L C u = (ofRecord D L Del h0).hA C (D.mem u).A.T := by
  have s : (∑ t ∈ D.host.TT, (((ofRecord D L Del h0).aT t : ℚ) : ℝ) * Real.log ((D.mem u).A.T : ℝ)) =
      ∑ t : D.host.TT, (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ) := by
    rw [← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl (fun t _ => by rw [ofRecord_aT D L Del h0 t])
  have hS : (ofRecord D L Del h0).Sc = L.Sc := by
    rw [L.Sc_eq, hDel]
    unfold NumDatum.Sc
    push_cast
    rfl
  have hE : (ofRecord D L Del h0).eta = L.etaSz := hEta.symm
  have e : (ofRecord D L Del h0).hA C (D.mem u).A.T =
      -(∑ t ∈ D.host.TT, (((ofRecord D L Del h0).aT t : ℚ) : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
        C * ((D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) +
          (D.R.f : ℝ) * ((D.R.m : ℝ) * (ofRecord D L Del h0).eta + (ofRecord D L Del h0).Sc) * (D.R.N D.R.m : ℝ) +
          (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) * (ofRecord D L Del h0).La := rfl
  rw [e, s, hS, hE, ofRecord_La]
  rfl

theorem ofRecord_exch : (ofRecord D L Del h0).exch = exch D := rfl

theorem ofRecord_EatC (c : ErrC) {j : ℕ} (hj : 1 ≤ j) (p : ℕ) :
    (ofRecord D L Del h0).EatC c.dig j p = EatC L c j p := by
  have s : (∑ z : Bool × HH D, (ofRecord D L Del h0).w j z) = ∑ τ : D.what₂.Tau, wj D j τ :=
    (Finset.sum_congr rfl (fun z _ => ofRecord_w D L Del h0 hj z)).trans
      ((tauPl_bijective D).sum_comp (fun τ => wj D j τ))
  have e : (ofRecord D L Del h0).EatC c.dig j p =
      c.dig * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a +
        (∑ z : Bool × HH D, (ofRecord D L Del h0).w j z) / ((p : ℝ) ^ 2 - 1) := rfl
  rw [e, s]
  rfl

theorem ofRecord_nuAbs (hDel : D.s.Del = (Del : ℚ)) (u : D.what₂.Word) (j : ℕ) (z : Bool × HH D) :
    (((ofRecord D L Del h0).nuAbs (letterOf D L Del h0 u) j z : ℚ) : ℝ) = nuAbs D u j (tauPl D z) := by
  unfold NumDatum.nuAbs nuAbs
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => ofRecord_nu D L Del h0 hDel u j z i)

theorem ofRecord_ctD (hDel : D.s.Del = (Del : ℚ)) (u : D.what₂.Word) (j : ℕ) (t : HH D) :
    (((ofRecord D L Del h0).ctD (letterOf D L Del h0 u) j t : ℚ) : ℝ) = ctD D u j t := by
  have a0 := ofRecord_nuAbs D L Del h0 hDel u j (false, t)
  have a1 := ofRecord_nu D L Del h0 hDel u j (false, t) 0
  have a2 := ofRecord_nu D L Del h0 hDel u j (false, t) 1
  have a3 := ofRecord_nu D L Del h0 hDel u j (true, t) 0
  unfold NumDatum.ctD ctD
  by_cases h : t ∈ D.host.TT
  · simp only [h, if_true]
    push_cast
    rw [a0, a1, a2, a3]
  · simp only [h, if_false, sub_zero, add_zero]
    exact a0

open Classical in

abbrev codeOf : Finset (Code (ofRecord D L Del h0)) := Finset.univ.image (letterOf D L Del h0)

theorem codeOf_nonempty : (codeOf D L Del h0).Nonempty :=
  ⟨letterOf D L Del h0 D.u₀, by unfold codeOf; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

theorem ofRecord_EatD (hDel : D.s.Del = (Del : ℚ)) {j : ℕ} (hj : 1 ≤ j) :
    (ofRecord D L Del h0).EatD (codeOf D L Del h0) (codeOf_nonempty D L Del h0) j = EatD D j := by
  unfold NumDatum.EatD EatD
  rw [ofRecord_FRamD D L Del h0 hj]
  congr 2
  rw [Finset.sup'_image]
  refine Finset.sup'_congr _ rfl (fun u _ => ?_)
  show (((∑ t : HH D, (ofRecord D L Del h0).ctD (letterOf D L Del h0 u) j t : ℚ)) : ℝ) = ∑ t : HH D, ctD D u j t
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl (fun t _ => ofRecord_ctD D L Del h0 hDel u j t)

theorem ofRecord_EatG (hK : DV.KapDef D) (hEta : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) (X : ErrX D) (c : ErrC) (i : Fin 2)
    (u : D.what₂.Word) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : D.what₂.places.Pl) (bar : Bool)
    (hv : vNN X i u j w = if bar then (((ofRecord D L Del h0).Dpi (letterOf D L Del h0 u) j : ℚ) : ℝ) else 0) :
    (ofRecord D L Del h0).EatG c.g (letterOf D L Del h0 u) j bar = EatG L X c i u j w := by
  have hE : (ofRecord D L Del h0).eta = L.etaSz := hEta.symm
  unfold NumDatum.EatG EatG
  rw [ofRecord_FTypeG D L Del h0 hK h1 h2, hv, hE]
  rfl

open Classical in
include hh in
theorem ofRecord_EatI (hDel : D.s.Del = (Del : ℚ)) (hEta : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) (K : Consts) (c : ErrC)
    {j : ℕ} (hj : 1 ≤ j) : (ofRecord D L Del h0).EatI c.c6 K.dl1 K.dl2 j p = EatI L K c j p := by
  have hS : (ofRecord D L Del h0).Sc = L.Sc := by
    rw [L.Sc_eq, hDel]
    unfold NumDatum.Sc
    push_cast
    rfl
  have hE : (ofRecord D L Del h0).eta = L.etaSz := hEta.symm
  have kA : (ofRecord D L Del h0).kindA p = kindA D p := rfl
  have kB : (ofRecord D L Del h0).kindBC p = kindBC D p := rfl
  have kT : (ofRecord D L Del h0).topsBC p = topsBC D p := by
    unfold NumDatum.topsBC Formalism.BasicNotions.topsBC
    rw [kB]
    ext z
    constructor <;> intro hz <;> rw [Finset.mem_filter] at hz ⊢ <;> exact hz
  have s1 : (∑ z ∈ kindA D p, (ofRecord D L Del h0).FOrb j p z) = ∑ z ∈ kindA D p, FOrb D j p z :=
    Finset.sum_congr rfl (fun z _ => ofRecord_FOrb D L Del h0 hh hj z)
  have s2 : (∑ z ∈ kindBC D p, (ofRecord D L Del h0).w j z) = ∑ z ∈ kindBC D p, wPl D j z :=
    Finset.sum_congr rfl (fun z _ => ofRecord_w D L Del h0 hj z)
  have hX : (ofRecord D L Del h0).EatX c.c6 j p = EatX L c j p := by
    have hc : (ofRecord D L Del h0).IsCs p ↔ IsCs D p := by
      unfold NumDatum.IsCs IsCs
      rw [hh]
      exact Iff.rfl
    unfold NumDatum.EatX EatX
    by_cases h : IsCs D p
    · rw [if_pos (hc.2 h), if_pos h, kB, s2]
      rfl
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
  unfold NumDatum.EatI EatI
  rw [hX, kA, kB, kT, s1, s2, ofRecord_ordP D L Del h0 hh, hS, hE]
  rfl

theorem errG_compare (N : NumDatum) (y : ℝ) (hy : 0 ≤ y) :
    (N.Nm : ℝ) ^ 2 + y ≤ (N.Nm : ℝ) * ((N.Nm : ℝ) + N.R.t) + y ∧
      (N.Nm : ℝ) * ((N.Nm : ℝ) + N.R.t) + y ≤ 2 * ((N.Nm : ℝ) ^ 2 + y) := by
  have hNt : N.R.t ≤ N.Nm := by
    unfold NumDatum.Nm Formalism.BasicNotions.Ranks.N
    calc N.R.t ≤ 2 * (N.R.t + 1) := by omega
      _ ≤ N.R.m * (N.R.t + 1) := Nat.mul_le_mul_right _ N.R.two_le_m
      _ ≤ N.R.k + N.R.m * (N.R.t + 1) := Nat.le_add_left _ _
  have hNt' : (N.R.t : ℝ) ≤ N.Nm := by exact_mod_cast hNt
  have h0 : (0 : ℝ) ≤ N.Nm := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hNt' h0]

theorem ofRecord_aPlus (j : ℕ) (z : Bool × HH D) (i : ℕ) :
    (ofRecord D L Del h0).aPlus j z i = DV.aPlusQ D j (tauPl D z) i := rfl

theorem ofRecord_aMinus (j : ℕ) (z : Bool × HH D) (c : ℕ) :
    (ofRecord D L Del h0).aMinus j z c = DV.aMinusQ D j (tauPl D z) c := rfl

end Record

theorem hostHypEx : HostHyp 11 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem layerEx : ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ζ a b : L), Formalism.TwoAdicCyclotomicDecomposition.IsLayer (2 + 2) 11 7 ζ a b :=
  Formalism.TwoAdicCyclotomicDecomposition.layerExists 4 11 7

def hostEx : Formalism.HC.HostAx Examples₂.R0.toFrame :=
  @Formalism.HC.D7.hostAx Examples₂.R0.toFrame Examples₂.exampleRanks_h_injective 11 7 hostHypEx le_rfl layerEx.choose layerEx.choose_spec.choose
    layerEx.choose_spec.choose_spec.choose _ _ _
    layerEx.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

theorem hostEx_q : hostEx.q = 11 := rfl
theorem hostEx_d : hostEx.d = 7 := rfl
theorem hostEx_QS : hostEx.QS = 16 := rfl
theorem hostEx_psQ : hostEx.toHostRaw.PsQ :=
  @Formalism.HC.D7.psQ Examples₂.R0.toFrame Examples₂.exampleRanks_h_injective 11 7 hostHypEx le_rfl layerEx.choose layerEx.choose_spec.choose
    layerEx.choose_spec.choose_spec.choose _ _ _
    layerEx.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

def numEx : NumDatum where
  R := Examples₂.R0
  sc := { x := 2, eps := 1 / 100, one_lt_alt := by norm_num, eps_pos := by norm_num, eps_lt := by norm_num,
          J := 1, one_le_J := le_rfl }
  H := hostEx
  g := ![3697, 7393]
  g_prime := by
    intro i
    fin_cases i
    · show Nat.Prime 3697
      norm_num
    · show Nat.Prime 7393
      norm_num
  TT := {0}
  Del := 1
  h0 := 18
  hc := fun _ => Examples₂.hc0

theorem ex_e : numEx.R.e = 2 := rfl
theorem ex_k : numEx.R.k = 8 := rfl
theorem ex_m : numEx.R.m = 2 := rfl
theorem numEx_t_eq_fifteen : numEx.R.t = 15 := rfl
theorem ex_nV : numEx.R.nV = 24 := rfl
theorem example_rank_first : numEx.R.N (1 - 1) = 8 := rfl
theorem example_rank_second : numEx.R.N 1 = 24 := rfl
theorem ex_Del : numEx.Del = 1 := rfl

theorem example_exponent_first (z : RPl numEx.R) : numEx.eQ 1 z = 100 := by
  rfl

theorem example_weight_first (z : RPl numEx.R) : numEx.w 1 z = 100 := by
  unfold NumDatum.w
  rw [example_exponent_first]
  norm_num

theorem ex_aPlus_first (z : RPl numEx.R) : numEx.aPlus 1 z 0 = 109 := by
  have hs : numEx.sigPar z 0 = 24 := rfl
  unfold NumDatum.aPlus
  rw [hs, example_exponent_first, ex_nV, ex_k, ex_m]
  norm_num

theorem ex_aPlus_last (z : RPl numEx.R) : numEx.aPlus 1 z 7 = 1 := by
  have hs : numEx.sigPar z 7 = -91 := rfl
  unfold NumDatum.aPlus
  rw [hs, example_exponent_first, ex_nV, ex_k, ex_m]
  norm_num

theorem ex_aMinus (z : RPl numEx.R) : numEx.aMinus 1 z 0 = 1 := by
  unfold NumDatum.aMinus
  rw [dif_pos (show 1 + 0 < numEx.R.m by decide)]
  change (109 : ℚ) - numEx.eQ 1 z - ((numEx.R.t : ℚ) + 1 + 2 * ((0 : ℕ) : ℚ)) / 2 = 1
  rw [example_exponent_first, numEx_t_eq_fifteen]
  norm_num

theorem ex_nu_first (δ : Code numEx) (z : RPl numEx.R) : numEx.nu δ 1 z 0 = 141 := by
  have h : (0 : ℕ) < numEx.R.k := by show 0 < 8; norm_num
  have h' : ¬ (1 ≤ (⟨0, h⟩ : Fin numEx.R.k).1 ∧ (⟨0, h⟩ : Fin numEx.R.k).1 + 1 < numEx.R.k) := by
    rintro ⟨a, -⟩; exact absurd a (by norm_num)
  unfold NumDatum.nu NumDatum.srcPar NumDatum.uW
  rw [dif_pos h, dif_neg h', example_exponent_first]
  have e1 : (numEx.hc z).u ⟨0, h⟩ = 113 / 2 := rfl
  rw [e1, example_rank_first, example_rank_second]
  norm_num

theorem ex_nu_second (δ : Code numEx) (z : RPl numEx.R) :
    numEx.nu δ 1 z 1 = if δ ⟨0, by show 0 < 8 - 2; norm_num⟩ then 108 else 109 := by
  have h : (1 : ℕ) < numEx.R.k := by show 1 < 8; norm_num
  have h' : 1 ≤ (⟨1, h⟩ : Fin numEx.R.k).1 ∧ (⟨1, h⟩ : Fin numEx.R.k).1 + 1 < numEx.R.k :=
    ⟨le_rfl, by show 1 + 1 < 8; norm_num⟩
  unfold NumDatum.nu NumDatum.srcPar NumDatum.uW
  rw [dif_pos h, dif_pos h', example_exponent_first]
  have e1 : (numEx.hc z).v ⟨(⟨1, h⟩ : Fin numEx.R.k).1 - 1, by show 1 - 1 < 8 - 1; norm_num⟩ = 24 := rfl
  rw [e1, example_rank_first, example_rank_second, ex_Del]
  by_cases hδ : δ ⟨0, by show 0 < 8 - 2; norm_num⟩ = true
  · rw [if_pos hδ, if_pos (show δ ⟨(⟨1, h⟩ : Fin numEx.R.k).1 - 1, _⟩ = true from hδ)]
    norm_num
  · rw [if_neg hδ, if_neg (show ¬ δ ⟨(⟨1, h⟩ : Fin numEx.R.k).1 - 1, _⟩ = true from hδ)]
    norm_num

theorem ex_FRamD : numEx.FRamD 1 = -1400 := by
  unfold NumDatum.FRamD
  simp only [example_weight_first, min_self, Finset.sum_const, Finset.card_univ]
  rw [Formalism.HC.Frame.card_A, show numEx.R.ord = 4 from rfl, ex_k]
  norm_num

theorem ex_FjP_d : numEx.FjP 1 7 = -1400 := by
  rw [numEx.FjP_d 1 (p := 7) (by show ¬ (7 = 3697 ∨ 7 = 7393); norm_num) (primeClass_d hostEx.toHostRaw), ex_FRamD]

theorem ex_FjP_2 : numEx.FjP 1 2 = 0 :=
  numEx.FjP_split 1 (p := 2) (by show ¬ (2 = 3697 ∨ 2 = 7393); norm_num) (Or.inr (Or.inl (primeClass_two hostEx.toHostRaw)))

theorem ex_FjP_q : numEx.FjP 1 11 = 0 :=
  numEx.FjP_split 1 (p := 11) (by show ¬ (11 = 3697 ∨ 11 = 7393); norm_num) (Or.inr (Or.inr (primeClass_q hostEx.toHostRaw)))

theorem ex_aT : numEx.aT 0 = 53 := by
  unfold NumDatum.aT
  have e1 : (numEx.hc (false, 0)).u ⟨0, by show 0 < 8; norm_num⟩ = 113 / 2 := rfl
  rw [e1, ex_k]
  norm_num

theorem example_prime_three_signal : numEx.cls 3 = PrimeClass.signal := by
  have h1 : jacobiSym (-((7 : ℕ) : ℤ)) 3 = -1 := by norm_num
  have h2 : jacobiSym (-((11 : ℕ) : ℤ)) 3 = 1 := by norm_num
  have hN : ¬ 3 ∣ hostEx.condN := by
    show ¬ 3 ∣ 16 * 11 * 7
    norm_num
  refine (primeClass_eq_signal_iff' (H := hostEx.toHostRaw) Nat.prime_three).2 ⟨hN, h1, ?_⟩
  rw [hostEx_psQ.psAt_prime Nat.prime_three hN]
  exact h2

end Formalism.L2.DIV

end
