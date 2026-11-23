import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete

namespace GlobalTheory.AwayNorm

variable {R N : Type} [CommRing R] [CommRing N] [Algebra R N]

def Dv (R : Type) [CommRing R] [Algebra R N] (u : Nˣ) (x : N) (r : ℤ) : Prop :=
  ∃ y : R, x = ((u ^ r : Nˣ) : N) * algebraMap R N y

variable {R N : Type} [CommRing R] [CommRing N] [Algebra R N] in

theorem _root_.GlobalTheory.AwayNorm.exists_normed_away : ∀ (p : ℕ) (R : Type) [CommRing R],
    2 ≤ p →
    _root_.GlobalTheory.Decompl.LAdic.Good p R →
    ∃ (N : Type) (_ : NormedCommRing N) (_ : CompleteSpace N) (_ : Algebra R N),
      IsLocalization.Away (p : R) N ∧
      (∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : R, x = (p : N) ^ r * algebraMap R N y) ∧
      ∀ x : N, ‖(p : N) * x‖ = (p : ℝ)⁻¹ * ‖x‖ := by
  intro p R _ hp hR
  obtain ⟨htf, hsep, hcomp⟩ := hR
  let L := Localization.Away (p : R)
  have hunit : IsUnit (algebraMap R L (p : R)) := IsLocalization.Away.algebraMap_isUnit (p : R)
  set u : Lˣ := hunit.unit with hu
  have hu' : (u : L) = (p : L) := by rw [hu, IsUnit.unit_spec, map_natCast]
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hpne : (p : ℝ)⁻¹ ≠ 0 := hp0.ne'
  have hpn : ∀ n : ℕ, ∀ x : R, (p : R) ^ n * x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply ih
      apply htf
      rw [← mul_assoc, ← pow_succ']
      exact hx
  have hinj : Function.Injective (algebraMap R L) := by
    refine IsLocalization.injective L (M := Submonoid.powers (p : R)) ?_
    rintro _ ⟨n, rfl⟩
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x hx => hpn n x hx, fun x hx => hpn n x (by rw [mul_comm]; exact hx)⟩
  obtain ⟨D, hD⟩ : ∃ D : L → ℤ → Prop,
      ∀ x r, D x r ↔ ∃ y : R, x = ((u ^ r : Lˣ) : L) * algebraMap R L y :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hDnat : ∀ (x : L) (n : ℕ), D x n ↔ ∃ y : R, x = (p : L) ^ n * algebraMap R L y := by
    intro x n
    rw [hD, zpow_natCast, Units.val_pow_eq_pow_val, hu']
  have hmono : ∀ x r s, s ≤ r → D x r → D x s := by
    intro x r s hsr hx
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = s + n := ⟨(r - s).toNat, by omega⟩
    rw [hD] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(p : R) ^ n * y, ?_⟩
    rw [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, hu', map_mul, map_pow,
      map_natCast]
    ring
  have hadd : ∀ x y r, D x r → D y r → D (x + y) r := by
    intro x y r hx hy
    rw [hD] at hx hy ⊢
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by rw [map_add, mul_add]⟩
  have hneg : ∀ x r, D x r → D (-x) r := by
    intro x r hx
    rw [hD] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨-a, by rw [map_neg, mul_neg]⟩
  have hmul : ∀ x y r s, D x r → D y s → D (x * y) (r + s) := by
    intro x y r s hx hy
    rw [hD] at hx hy ⊢
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, by rw [zpow_add, Units.val_mul, map_mul]; ring⟩
  have hup : ∀ x r, D x r → D ((p : L) * x) (r + 1) := by
    intro x r hx
    rw [hD] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rw [zpow_add_one, Units.val_mul, hu']; ring⟩
  have hdown : ∀ x r, D ((p : L) * x) r → D x (r - 1) := by
    intro x r hx
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
    rw [add_sub_cancel_right]
    rw [hD] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    have hpu : IsUnit (p : L) := hu' ▸ u.isUnit
    apply hpu.mul_left_cancel
    rw [ha, zpow_add_one, Units.val_mul, hu']
    ring
  have hex : ∀ x : L, ∃ r, D x r := by
    intro x
    obtain ⟨z, hz⟩ := IsLocalization.surj (Submonoid.powers (p : R)) x
    obtain ⟨n, hn⟩ := z.2.2
    refine ⟨-(n : ℤ), ?_⟩
    rw [hD]
    refine ⟨z.1, ?_⟩
    rw [← hz, ← hn, map_pow, map_natCast, ← hu', zpow_neg, zpow_natCast,
      ← Units.val_pow_eq_pow_val, mul_comm x, Units.inv_mul_cancel_left]
  have hzero : ∀ r, D 0 r := fun r => (hD 0 r).2 ⟨0, by simp⟩
  have hsepL : ∀ x : L, (∀ n : ℕ, D x n) → x = 0 := by
    intro x hx
    obtain ⟨y0, hy0⟩ := (hDnat x 0).1 (hx 0)
    rw [pow_zero, one_mul] at hy0
    have hy : y0 = 0 := by
      apply hsep
      intro k
      obtain ⟨yk, hyk⟩ := (hDnat x k).1 (hx k)
      refine ⟨yk, hinj ?_⟩
      rw [← hy0, hyk, map_mul, map_pow, map_natCast]
    rw [hy0, hy, map_zero]

  let nrm : L → ℝ := fun x => ⨅ r : {r : ℤ // D x r}, (p : ℝ)⁻¹ ^ (r : ℤ)
  have hne : ∀ x, Nonempty {r : ℤ // D x r} := fun x =>
    let ⟨r, hr⟩ := hex x
    ⟨⟨r, hr⟩⟩
  have hbdd : ∀ x, BddBelow (Set.range fun r : {r : ℤ // D x r} => (p : ℝ)⁻¹ ^ (r : ℤ)) :=
    fun x => ⟨0, by rintro _ ⟨r, rfl⟩; positivity⟩
  have hle1 : ∀ x r, D x r → nrm x ≤ (p : ℝ)⁻¹ ^ r := fun x r h =>
    ciInf_le (hbdd x) ⟨r, h⟩
  have hge1 : ∀ x (c : ℝ), (∀ r, D x r → c ≤ (p : ℝ)⁻¹ ^ r) → c ≤ nrm x := by
    intro x c h
    haveI := hne x
    exact le_ciInf fun r => h r.1 r.2
  have hnn : ∀ x, 0 ≤ nrm x := fun x => hge1 x 0 fun r _ => by positivity
  have hlow : ∀ x r, ¬ D x r → (p : ℝ)⁻¹ ^ (r - 1) ≤ nrm x := by
    intro x r hr
    refine hge1 x _ fun s hs => ?_
    have hsr : s ≤ r - 1 := by
      by_contra h
      exact hr (hmono x s r (by omega) hs)
    exact zpow_le_zpow_right_of_le_one₀ hp0 hp1.le hsr
  have hchar : ∀ x r, nrm x ≤ (p : ℝ)⁻¹ ^ r ↔ D x r := by
    intro x r
    refine ⟨fun h => ?_, hle1 x r⟩
    by_contra hr
    have h1 := hlow x r hr
    have h2 : (p : ℝ)⁻¹ ^ r < (p : ℝ)⁻¹ ^ (r - 1) :=
      zpow_lt_zpow_right_of_lt_one₀ hp0 hp1 (by omega)
    linarith
  have hnz : nrm 0 = 0 := by
    refine le_antisymm ?_ (hnn 0)
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h hp1
    have := hle1 0 n (hzero n)
    rw [zpow_natCast] at this
    linarith
  have hnorm_mono : ∀ x y, (∀ r, D x r → D y r) → nrm y ≤ nrm x := fun x y h =>
    hge1 x _ fun r hr => hle1 y r (h r hr)
  have hnneg : ∀ x, nrm (-x) = nrm x := fun x =>
    le_antisymm (hnorm_mono _ _ fun r hr => hneg x r hr)
      (hnorm_mono _ _ fun r hr => by have := hneg (-x) r hr; rwa [neg_neg] at this)
  have hnadd : ∀ x y, nrm (x + y) ≤ nrm x + nrm y := by
    intro x y
    have key : ∀ r s, D x r → D y s →
        nrm (x + y) ≤ (p : ℝ)⁻¹ ^ r + (p : ℝ)⁻¹ ^ s := by
      intro r s hr hs
      have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ r := by positivity
      have hs0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ s := by positivity
      rcases le_total r s with h | h
      · have := hle1 _ _ (hadd x y r hr (hmono y s r h hs))
        linarith
      · have := hle1 _ _ (hadd x y s (hmono x r s h hr) hs)
        linarith
    have h1 : ∀ s, D y s → nrm (x + y) - (p : ℝ)⁻¹ ^ s ≤ nrm x := fun s hs =>
      hge1 x _ fun r hr => by have := key r s hr hs; linarith
    have h2 : nrm (x + y) - nrm x ≤ nrm y :=
      hge1 y _ fun s hs => by have := h1 s hs; linarith
    linarith
  have hnmul : ∀ x y, nrm (x * y) ≤ nrm x * nrm y := by
    intro x y
    have key : ∀ r s, D x r → D y s → nrm (x * y) ≤ (p : ℝ)⁻¹ ^ r * (p : ℝ)⁻¹ ^ s := by
      intro r s hr hs
      rw [← zpow_add₀ hpne]
      exact hle1 _ _ (hmul x y r s hr hs)
    have h1 : ∀ s, D y s → nrm (x * y) ≤ nrm x * (p : ℝ)⁻¹ ^ s := by
      intro s hs
      have hq : (0 : ℝ) < (p : ℝ)⁻¹ ^ s := by positivity
      rw [← div_le_iff₀ hq]
      exact hge1 x _ fun r hr => by rw [div_le_iff₀ hq]; exact key r s hr hs
    rcases (hnn x).eq_or_lt with h0 | h0
    · obtain ⟨s, hs⟩ := hex y
      have := h1 s hs
      rw [← h0, zero_mul] at this
      rw [← h0, zero_mul]
      exact this
    · rw [← div_le_iff₀' h0]
      exact hge1 y _ fun s hs => by rw [div_le_iff₀' h0]; exact h1 s hs
  have hnpos : ∀ x, nrm x = 0 → x = 0 := fun x h =>
    hsepL x fun n => (hchar x n).1 (by rw [h]; positivity)
  let f : RingNorm L :=
    { toFun := nrm
      map_zero' := hnz
      add_le' := hnadd
      neg' := hnneg
      mul_le' := hnmul
      eq_zero_of_map_eq_zero' := hnpos }
  letI inst : NormedCommRing L := { f.toNormedRing with mul_comm := mul_comm }
  have hnorm : ∀ x : L, ‖x‖ = nrm x := fun _ => rfl
  have hcharN : ∀ (x : L) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔
      ∃ y : R, x = (p : L) ^ r * algebraMap R L y := by
    intro x r
    rw [hnorm, ← zpow_natCast, hchar, hDnat]
  have hcomplete : CompleteSpace L := by
    refine Metric.complete_of_convergent_controlled_sequences (fun n => (p : ℝ)⁻¹ ^ n)
      (fun n => pow_pos hp0 n) fun v hv => ?_
    have hstep : ∀ k : ℕ, ∃ z : R, v (k + 1) - v k = (p : L) ^ (k + 1) * algebraMap R L z := by
      intro k
      rw [← hDnat]
      by_contra h
      have h1 := hlow _ _ h
      rw [Nat.cast_succ, add_sub_cancel_right, zpow_natCast] at h1
      have h2 := hv k (k + 1) k (Nat.le_succ k) le_rfl
      rw [dist_eq_norm, hnorm] at h2
      linarith
    choose z hz using hstep
    obtain ⟨s, hs⟩ := hcomp z
    choose r hr using hs
    have htel : ∀ n, v n = v 0 + (p : L) *
        algebraMap R L (∑ i ∈ Finset.range n, (p : R) ^ i * z i) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, map_add, mul_add, ← add_assoc, ← ih, map_mul, map_pow,
          map_natCast]
        linear_combination hz n
    refine ⟨v 0 + (p : L) * algebraMap R L s, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hp1
    refine ⟨M, fun n hn => ?_⟩
    have hdiff : v n - (v 0 + (p : L) * algebraMap R L s) =
        (p : L) ^ (n + 1) * algebraMap R L (-r n) := by
      rw [htel n, map_neg]
      have := congrArg (algebraMap R L) (hr n)
      rw [map_sub, map_mul, map_pow, map_natCast] at this
      linear_combination (-(p : L)) * this
    have hb : ‖v n - (v 0 + (p : L) * algebraMap R L s)‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) :=
      (hcharN _ _).2 ⟨_, hdiff⟩
    have hc : (p : ℝ)⁻¹ ^ (n + 1) ≤ (p : ℝ)⁻¹ ^ M :=
      pow_le_pow_of_le_one hp0.le hp1.le (by omega)
    rw [dist_eq_norm]
    linarith
  refine ⟨L, inst, hcomplete, inferInstance, inferInstance, hcharN, fun x => ?_⟩
  rw [hnorm, hnorm]
  refine le_antisymm ?_ ?_
  · have h : nrm ((p : L) * x) / (p : ℝ)⁻¹ ≤ nrm x :=
      hge1 x _ fun r hr => by
        rw [div_le_iff₀ hp0, ← zpow_add_one₀ hpne]
        exact hle1 _ _ (hup x r hr)
    rw [div_le_iff₀ hp0] at h
    linarith
  · refine hge1 _ _ fun r hr => ?_
    have h := hle1 _ _ (hdown x r hr)
    have e : (p : ℝ)⁻¹ ^ r = (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ (r - 1) := by
      rw [mul_comm, ← zpow_add_one₀ hpne, sub_add_cancel]
    rw [e]
    exact mul_le_mul_of_nonneg_left h hp0.le

end GlobalTheory.AwayNorm
