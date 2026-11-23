import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete

open Filter Topology

namespace GlobalTheory.WittRootsOfUnity

theorem add_pow_of_cast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (h0 : (p : A) = 0)
    (a b : A) (m : ℕ) : (a + b) ^ p ^ m = a ^ p ^ m + b ^ p ^ m := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  ·
    have : Fact p.Prime := ⟨hp⟩
    have : CharP A p := (CharP.charP_iff_prime_eq_zero hp).2 h0
    exact add_pow_char_pow ..

theorem neg_pow_of_cast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (h0 : (p : A) = 0)
    (a : A) (m : ℕ) : (-a) ^ p ^ m = -a ^ p ^ m := by

  have h := add_pow_of_cast_eq_zero hp h0 a (-a) m
  rw [add_neg_cancel, zero_pow (pow_ne_zero _ hp.ne_zero)] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

def mu (K : Type*) [Field K] (p : ℕ) : Set K := {ζ | ∃ n, 0 < n ∧ n.Coprime p ∧ ζ ^ n = 1}

private theorem pow_pow_eq_self_of_pow_eq_self {A : Type*} [Monoid A] {q : ℕ} {a : A} (h : a ^ q = a) (k : ℕ) :
    a ^ q ^ k = a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, h]

private theorem frobenius_periodic_add_and_mul {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (h0 : (p : A) = 0)
    {a b : A} (ha : ∃ f, 0 < f ∧ a ^ p ^ f = a) (hb : ∃ f, 0 < f ∧ b ^ p ^ f = b) :
    (∃ f, 0 < f ∧ (a + b) ^ p ^ f = a + b) ∧ (∃ f, 0 < f ∧ (a * b) ^ p ^ f = a * b) := by
  obtain ⟨f, hf, ha⟩ := ha
  obtain ⟨g, hg, hb⟩ := hb

  have ha' : a ^ p ^ (f * g) = a := by rw [pow_mul]; exact pow_pow_eq_self_of_pow_eq_self ha g
  have hb' : b ^ p ^ (f * g) = b := by rw [mul_comm, pow_mul]; exact pow_pow_eq_self_of_pow_eq_self hb f
  exact ⟨⟨f * g, Nat.mul_pos hf hg, by rw [add_pow_of_cast_eq_zero hp h0, ha', hb']⟩,
    ⟨f * g, Nat.mul_pos hf hg, by rw [mul_pow, ha', hb']⟩⟩

private theorem exists_frobenius_periodic_of_mem_mu {K : Type*} [Field K] {p : ℕ} {ζ : K} (hζ : ζ ∈ mu K p) :
    ∃ f, 0 < f ∧ ζ ^ p ^ f = ζ := by
  obtain ⟨n, hn, hcop, h1⟩ := hζ

  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have hmod : p ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop.symm
  rw [pow_eq_pow_mod _ h1, hmod, ← pow_eq_pow_mod _ h1, pow_one]

theorem frob_periodic {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) {x : K}
    (hx : x ∈ Subring.closure (mu K p)) :
    ∃ f, 0 < f ∧ ∃ s ∈ Subring.closure (mu K p), x ^ p ^ f - x = p * s := by

  let I : Ideal (Subring.closure (mu K p)) := Ideal.span {((p : ℕ) : Subring.closure (mu K p))}
  have h0 : ((p : ℕ) : Subring.closure (mu K p) ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have key : ∀ (y : K) (hy : y ∈ Subring.closure (mu K p)),
      ∃ f, 0 < f ∧ (Ideal.Quotient.mk I ⟨y, hy⟩) ^ p ^ f = Ideal.Quotient.mk I ⟨y, hy⟩ := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨f, hf, hz'⟩ := exists_frobenius_periodic_of_mem_mu hz
      refine ⟨f, hf, ?_⟩
      rw [← map_pow]
      congr 1
      exact Subtype.ext (by simpa using hz')
    | zero =>
      refine ⟨1, one_pos, ?_⟩
      show (Ideal.Quotient.mk I 0) ^ p ^ 1 = Ideal.Quotient.mk I 0
      rw [map_zero, zero_pow (pow_ne_zero _ hp.ne_zero)]
    | one =>
      refine ⟨1, one_pos, ?_⟩
      show (Ideal.Quotient.mk I 1) ^ p ^ 1 = Ideal.Quotient.mk I 1
      rw [map_one, one_pow]
    | add z w hz hw ihz ihw =>
      obtain ⟨f, hf, h⟩ := (frobenius_periodic_add_and_mul hp h0 ihz ihw).1
      refine ⟨f, hf, ?_⟩
      show (Ideal.Quotient.mk I (⟨z, hz⟩ + ⟨w, hw⟩)) ^ p ^ f = Ideal.Quotient.mk I (⟨z, hz⟩ + ⟨w, hw⟩)
      rw [map_add]
      exact h
    | neg z hz ih =>
      obtain ⟨f, hf, h⟩ := ih
      refine ⟨f, hf, ?_⟩
      show (Ideal.Quotient.mk I (-⟨z, hz⟩)) ^ p ^ f = Ideal.Quotient.mk I (-⟨z, hz⟩)
      rw [map_neg, neg_pow_of_cast_eq_zero hp h0, h]
    | mul z w hz hw ihz ihw =>
      obtain ⟨f, hf, h⟩ := (frobenius_periodic_add_and_mul hp h0 ihz ihw).2
      refine ⟨f, hf, ?_⟩
      show (Ideal.Quotient.mk I (⟨z, hz⟩ * ⟨w, hw⟩)) ^ p ^ f = Ideal.Quotient.mk I (⟨z, hz⟩ * ⟨w, hw⟩)
      rw [map_mul]
      exact h
  obtain ⟨f, hf, h⟩ := key x hx
  rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨f, hf, c, c.2, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

section Normed

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {p : ℕ}

def W (K : Type*) [NormedField K] (p : ℕ) : Subring K :=
  (Subring.closure (mu K p)).topologicalClosure

omit [IsUltrametricDist K] in
theorem isClosed_divisorComponent : IsClosed (W K p : Set K) :=
  Subring.isClosed_topologicalClosure _

omit [IsUltrametricDist K] in
theorem mem_W_of_mem {x : K} (hx : x ∈ Subring.closure (mu K p)) : x ∈ W K p :=
  Subring.le_topologicalClosure _ hx

omit [IsUltrametricDist K] in
theorem mem_closure_roots_of_unity {x : K} (hx : x ∈ W K p) :
    x ∈ closure (Subring.closure (mu K p) : Set K) :=
  hx

theorem norm_le_one_of_mem {x : K} (hx : x ∈ Subring.closure (mu K p)) : ‖x‖ ≤ 1 := by
  induction hx using Subring.closure_induction with
  | mem z hz =>

    obtain ⟨n, hn, -, h1⟩ := hz
    have : ‖z‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this).le
  | zero => simp
  | one => simp
  | add z w _ _ hz hw => exact (IsUltrametricDist.norm_add_le_max z w).trans (max_le hz hw)
  | neg z _ hz => rwa [norm_neg]
  | mul z w _ _ hz hw => rw [norm_mul]; exact mul_le_one₀ hz (norm_nonneg w) hw

theorem norm_le_one_of_mem_W {x : K} (hx : x ∈ W K p) : ‖x‖ ≤ 1 :=
  closure_minimal (fun y hy => norm_le_one_of_mem hy) (isClosed_le continuous_norm continuous_const)
    (mem_closure_roots_of_unity hx)

omit [IsUltrametricDist K] in
theorem inv_one_sub_mem {u : K} (hu : u ∈ W K p) (h1 : ‖u‖ < 1) : (1 - u)⁻¹ ∈ W K p := by
  have hu1 : (1 - u) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at h1
    exact lt_irrefl _ h1

  have hsum : ∀ N, ∑ i ∈ Finset.range N, u ^ i = (1 - u)⁻¹ * (1 - u ^ N) := fun N =>
    (eq_inv_mul_iff_mul_eq₀ hu1).2 (mul_neg_geom_sum u N)
  have ht : Tendsto (fun N => ∑ i ∈ Finset.range N, u ^ i) atTop (𝓝 (1 - u)⁻¹) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).const_sub 1).const_mul (1 - u)⁻¹
    simp only [sub_zero, mul_one] at this
    simpa only [hsum] using this
  exact (isClosed_divisorComponent (K := K) (p := p)).mem_of_tendsto ht
    (Eventually.of_forall fun N => sum_mem fun i _ => pow_mem hu i)

omit [IsUltrametricDist K] in
theorem div_mem_of_mem (hp : p.Prime) {r : K} (hr : r ∈ Subring.closure (mu K p)) (h1 : ‖r‖ < 1) :
    r / p ∈ W K p := by
  by_cases hp0 : (p : K) = 0
  · rw [hp0, div_zero]; exact zero_mem _
  obtain ⟨f, hf, s, hs, hfs⟩ := frob_periodic hp hr
  obtain ⟨t, ht⟩ : ∃ t, p ^ f = t + 2 := ⟨p ^ f - 2, by have := Nat.one_lt_pow hf.ne' hp.one_lt; omega⟩

  have hu1 : ‖r ^ (t + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h1 (Nat.succ_ne_zero t)
  have h1u : (1 - r ^ (t + 1)) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at hu1
    exact lt_irrefl _ hu1
  have e1 : r * (1 - r ^ (t + 1)) = -(p * s) := by
    rw [ht] at hfs
    linear_combination (-1 : K) * hfs
  have key : r / p = -s * (1 - r ^ (t + 1))⁻¹ := by
    refine div_eq_of_eq_mul hp0 ?_
    calc r = r * (1 - r ^ (t + 1)) * (1 - r ^ (t + 1))⁻¹ := (mul_inv_cancel_right₀ h1u r).symm
      _ = -(p * s) * (1 - r ^ (t + 1))⁻¹ := by rw [e1]
      _ = -s * (1 - r ^ (t + 1))⁻¹ * p := by ring
  rw [key]
  exact mul_mem (neg_mem (mem_W_of_mem hs)) (inv_one_sub_mem (mem_W_of_mem (pow_mem hr _)) hu1)

omit [IsUltrametricDist K] in

theorem div_mem (hp : p.Prime) {w : K} (hw : w ∈ W K p) (h1 : ‖w‖ < 1) : w / p ∈ W K p := by

  have hw' : w ∈ closure ({y : K | ‖y‖ < 1} ∩ (Subring.closure (mu K p) : Set K)) :=
    (isOpen_lt continuous_norm continuous_const).inter_closure ⟨h1, mem_closure_roots_of_unity hw⟩
  have := map_mem_closure (t := (W K p : Set K)) (continuous_id.div_const (p : K)) hw'
    fun y hy => div_mem_of_mem hp hy.2 hy.1
  rw [isClosed_divisorComponent.closure_eq] at this
  exact this

theorem inv_mem_of_mem (hp : p.Prime) (hpn : ‖(p : K)‖ < 1) {r : K}
    (hr : r ∈ Subring.closure (mu K p)) (h1 : ‖r‖ = 1) : r⁻¹ ∈ W K p := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨f, hf, s, hs, hfs⟩ := frob_periodic hp hr
  obtain ⟨t, ht⟩ : ∃ t, p ^ f = t + 2 := ⟨p ^ f - 2, by have := Nat.one_lt_pow hf.ne' hp.one_lt; omega⟩
  have e1 : r * (r ^ (t + 1) - 1) = p * s := by
    rw [ht] at hfs
    linear_combination hfs

  have hn : ‖1 - r ^ (t + 1)‖ < 1 := by
    have h2 : ‖r‖ * ‖r ^ (t + 1) - 1‖ = ‖(p : K)‖ * ‖s‖ := by rw [← norm_mul, ← norm_mul, e1]
    rw [h1, one_mul] at h2
    rw [norm_sub_rev, h2]
    calc ‖(p : K)‖ * ‖s‖ ≤ ‖(p : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_le_one_of_mem hs) (norm_nonneg _)
      _ < 1 := by rwa [mul_one]
  have hinv : (r ^ (t + 1))⁻¹ ∈ W K p := by
    have := inv_one_sub_mem (sub_mem (one_mem _) (mem_W_of_mem (pow_mem hr (t + 1)))) hn
    rwa [sub_sub_cancel] at this
  have e2 : r⁻¹ = r ^ t * (r ^ (t + 1))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hr0), pow_succ', inv_mul_cancel_left₀ hr0]
  rw [e2]
  exact mul_mem (mem_W_of_mem (pow_mem hr t)) hinv

theorem inv_mem (hp : p.Prime) (hpn : ‖(p : K)‖ < 1) {w : K} (hw : w ∈ W K p) (h1 : ‖w‖ = 1) :
    w⁻¹ ∈ W K p := by

  obtain ⟨r, hr, hd⟩ := Metric.mem_closure_iff.1 (mem_closure_roots_of_unity hw) 1 one_pos
  have hd' : ‖r - w‖ < 1 := by rwa [dist_eq_norm, norm_sub_rev] at hd
  have hr1 : ‖r‖ = 1 := by
    apply le_antisymm
    · calc ‖r‖ = ‖w + (r - w)‖ := by rw [add_sub_cancel]
        _ ≤ max ‖w‖ ‖r - w‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := max_le h1.le hd'.le
    · by_contra hlt
      push_neg at hlt
      have : ‖w‖ < 1 :=
        calc ‖w‖ = ‖r + (w - r)‖ := by rw [add_sub_cancel]
          _ ≤ max ‖r‖ ‖w - r‖ := IsUltrametricDist.norm_add_le_max _ _
          _ < 1 := max_lt hlt (by rwa [norm_sub_rev])
      linarith
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr1
  have hri : r⁻¹ ∈ W K p := inv_mem_of_mem hp hpn hr hr1
  have ht : (r - w) * r⁻¹ ∈ W K p := mul_mem (sub_mem (mem_W_of_mem hr) hw) hri
  have htn : ‖(r - w) * r⁻¹‖ < 1 := by rw [norm_mul, norm_inv, hr1, inv_one, mul_one]; exact hd'
  have hweq : (1 - (r - w) * r⁻¹) * r = w := by
    rw [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hr0, mul_one, sub_sub_cancel]
  rw [← hweq, mul_inv]
  exact mul_mem (inv_one_sub_mem ht htn) hri

omit [IsUltrametricDist K] in
theorem mem_W_of_norm_le (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hpn : ‖(p : K)‖ < 1) (k : ℕ) :
    ∀ {x : K}, (p : K) ^ k * x ∈ W K p → ‖x‖ ≤ 1 → x ∈ W K p := by

  induction k with
  | zero => intro x hx _; simpa using hx
  | succ k ih =>
    intro x hx hx1
    apply ih _ hx1
    have hn : ‖(p : K) ^ (k + 1) * x‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc ‖(p : K)‖ ^ (k + 1) * ‖x‖ ≤ ‖(p : K)‖ ^ (k + 1) * 1 :=
            mul_le_mul_of_nonneg_left hx1 (by positivity)
        _ < 1 := by rw [mul_one]; exact pow_lt_one₀ (norm_nonneg _) hpn (Nat.succ_ne_zero k)
    have := div_mem hp hx hn
    rwa [pow_succ, mul_comm ((p : K) ^ k) (p : K), mul_assoc, mul_div_cancel_left₀ _ hp0] at this

theorem exists_unit (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hpn : ‖(p : K)‖ < 1) {w : K}
    (hw : w ∈ W K p) (hw0 : w ≠ 0) : ∃ k : ℕ, w / p ^ k ∈ W K p ∧ ‖w / p ^ k‖ = 1 := by
  by_contra hcon
  push_neg at hcon

  have hall : ∀ k : ℕ, w / (p : K) ^ k ∈ W K p := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      have hlt : ‖w / (p : K) ^ k‖ < 1 := lt_of_le_of_ne (norm_le_one_of_mem_W ih) (hcon k ih)
      have := div_mem hp ih hlt
      rwa [div_div, ← pow_succ] at this
  have hle : ∀ k : ℕ, ‖w‖ ≤ ‖(p : K)‖ ^ k := by
    intro k
    have h := norm_le_one_of_mem_W (hall k)
    have hpos : 0 < ‖(p : K)‖ ^ k := pow_pos (norm_pos_iff.2 hp0) k
    rwa [norm_div, norm_pow, div_le_one hpos] at h
  have : ‖w‖ ≤ 0 := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hpn) hle
  exact hw0 (norm_le_zero_iff.1 this)

def F (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hpn : ‖(p : K)‖ < 1) : Subfield K where
  carrier := {x | ∃ k : ℕ, (p : K) ^ k * x ∈ W K p}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have e : (p : K) ^ (k + l) * (a + b) = p ^ l * (p ^ k * a) + p ^ k * (p ^ l * b) := by ring
    rw [e]
    exact add_mem (mul_mem (pow_mem (natCast_mem _ _) _) hk) (mul_mem (pow_mem (natCast_mem _ _) _) hl)
  mul_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have e : (p : K) ^ (k + l) * (a * b) = (p ^ k * a) * (p ^ l * b) := by ring
    rw [e]
    exact mul_mem hk hl
  neg_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨k, by rw [mul_neg]; exact neg_mem hk⟩
  inv_mem' := by
    rintro a ⟨k, hk⟩
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    obtain ⟨l, hl, hl1⟩ := exists_unit hp hp0 hpn hk (mul_ne_zero (pow_ne_zero _ hp0) ha)
    refine ⟨l, ?_⟩
    have e : (p : K) ^ l * a⁻¹ = p ^ k * (p ^ k * a / p ^ l)⁻¹ := by field_simp
    rw [e]
    exact mul_mem (pow_mem (natCast_mem _ _) _) (inv_mem hp hpn hl hl1)

theorem isClosed_F (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hpn : ‖(p : K)‖ < 1) :
    IsClosed (F hp hp0 hpn : Set K) := by

  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (‖x‖ + 1)) hpn
  have hx1 : 0 < ‖x‖ + 1 := by positivity
  rw [lt_div_iff₀ hx1] at hk
  have hx' : x ∈ closure ({y : K | ‖y - x‖ < 1} ∩ (F hp hp0 hpn : Set K)) :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).inter_closure ⟨by simp, hx⟩
  have hmap : Set.MapsTo (fun y => (p : K) ^ k * y) ({y : K | ‖y - x‖ < 1} ∩ (F hp hp0 hpn : Set K))
      (W K p : Set K) := by
    rintro y ⟨hy1, hy2⟩
    have hy1' : ‖y - x‖ < 1 := hy1
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (p : K) ^ j * y ∈ W K p := hy2
    have hyn : ‖y‖ ≤ ‖x‖ + 1 := by
      calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by linarith
    apply mem_W_of_norm_le hp hp0 hpn j
    · have e : (p : K) ^ j * ((p : K) ^ k * y) = (p : K) ^ k * ((p : K) ^ j * y) := by ring
      rw [e]
      exact mul_mem (pow_mem (natCast_mem _ _) _) hj
    · rw [norm_mul, norm_pow]
      calc ‖(p : K)‖ ^ k * ‖y‖ ≤ ‖(p : K)‖ ^ k * (‖x‖ + 1) :=
            mul_le_mul_of_nonneg_left hyn (by positivity)
        _ ≤ 1 := hk.le
  have := map_mem_closure (continuous_const.mul continuous_id) hx' hmap
  rw [isClosed_divisorComponent.closure_eq] at this
  exact (show ∃ k : ℕ, (p : K) ^ k * x ∈ W K p from ⟨k, this⟩)

end Normed

theorem norm_p_lt_one {p : ℕ} [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by

  have h := PadicComplex.norm_extends' (p := p) (p : ℚ_[p])
  push_cast at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem inWf_of_mem_Kur {p : ℕ} [inst : Fact (Nat.Prime p)] {x : ℂ_[p]}
    (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) : Formalism.MainNotions.GL3Theta.InWf x := by

  have hp : p.Prime := inst.out
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hsub : Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ≤ F hp hp0 norm_p_lt_one := by
    refine Subfield.topologicalClosure_minimal _ ?_ (isClosed_F hp hp0 norm_p_lt_one)
    refine Subfield.closure_le.2 fun ζ hζ => ?_
    obtain ⟨n, hn, hnd, h1⟩ := hζ
    have hmu : ζ ∈ mu ℂ_[p] p := ⟨n, hn, ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm, h1⟩
    exact ⟨0, by simpa using mem_W_of_mem (Subring.subset_closure hmu)⟩
  exact hsub hx

end GlobalTheory.WittRootsOfUnity
