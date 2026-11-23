import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.PreOfGens
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsLiftAndAug

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries

variable {B : Type} [CommRing B]

theorem e_pow (Q : PDPoly B) (l n : ℕ) :
    ∃ M : ℕ, M * l.factorial ^ n = (n * l).factorial ∧ Q.e l ^ n = (M : Q.P) * Q.e (n * l) := by
  induction n with
  | zero => exact ⟨1, by simp, by simp [Q.e_zero]⟩
  | succ n ih =>
    obtain ⟨M, h1, h2⟩ := ih
    refine ⟨M * (n * l + l).choose (n * l), ?_, ?_⟩
    · have := Nat.add_choose_mul_factorial_mul_factorial (n * l) l
      rw [← Nat.choose_symm_add] at this
      rw [Nat.succ_mul, ← this, ← h1]; ring
    · rw [pow_succ, h2, mul_assoc, Q.e_mul, Nat.succ_mul]; push_cast; ring

theorem choose_fac (a b : ℕ) : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rwa [Nat.add_sub_cancel_left] at h

theorem num1 (m n : ℕ) {K : ℕ} (hK : K ≠ 0) :
    m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) =
      (m + n).choose m * (m + n).uniformBell K := by
  have hm := Nat.uniformBell_mul_eq m hK
  have hn := Nat.uniformBell_mul_eq n hK
  have hmn := Nat.uniformBell_mul_eq (m + n) hK
  have c1 := choose_fac (m * K) (n * K)
  have c2 := choose_fac m n
  have hpos : 0 < K.factorial ^ (m + n) * m.factorial * n.factorial := by positivity
  have e1 : m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) *
      (K.factorial ^ (m + n) * m.factorial * n.factorial) = (m * K + n * K).factorial := by
    rw [← c1, ← hm, ← hn]
    ring
  have e2 : (m + n).choose m * (m + n).uniformBell K *
      (K.factorial ^ (m + n) * m.factorial * n.factorial) = (m * K + n * K).factorial := by
    rw [← add_mul, ← hmn, ← c2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)

theorem num2 (n l M : ℕ) {K : ℕ} (hK : K ≠ 0) (hM : M * l.factorial ^ n = (n * l).factorial) :
    M * n.uniformBell K * (n * l + n * K).choose (n * l) = (l + K).choose l ^ n * n.uniformBell (l + K) := by
  have h1 := Nat.uniformBell_mul_eq n hK
  have h3 := Nat.uniformBell_mul_eq n (show l + K ≠ 0 by omega)
  have h4 := choose_fac (n * l) (n * K)
  have h5 := choose_fac l K
  have hpos : 0 < l.factorial ^ n * K.factorial ^ n * n.factorial := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc _ = (n * l + n * K).choose (n * l) * (M * l.factorial ^ n) *
        (n.uniformBell K * K.factorial ^ n * n.factorial) := by ring
    _ = (n * (l + K)).factorial := by rw [h1, hM, h4, mul_add]
    _ = n.uniformBell (l + K) * ((l + K).choose l * l.factorial * K.factorial) ^ n * n.factorial := by
        rw [h5, h3]
    _ = _ := by ring

def gb (Q : PDPoly B) (K n : ℕ) : Q.P := (n.uniformBell K : Q.P) * Q.e (n * K)

theorem gb_zero (Q : PDPoly B) (K : ℕ) : gb Q K 0 = 1 := by simp [gb, Nat.uniformBell_zero_left, Q.e_zero]

theorem gb_mul (Q : PDPoly B) {K : ℕ} (hK : K ≠ 0) (m n : ℕ) :
    gb Q K m * gb Q K n = ((m + n).choose m : Q.P) * gb Q K (m + n) := by
  unfold gb
  have h := num1 m n hK
  calc ((m.uniformBell K : Q.P) * Q.e (m * K)) * ((n.uniformBell K : Q.P) * Q.e (n * K))
      = ((m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) : ℕ) : Q.P) *
          Q.e (m * K + n * K) := by
        rw [mul_mul_mul_comm, Q.e_mul]
        push_cast
        ring
    _ = _ := by
        rw [h, ← add_mul]
        push_cast
        ring

private theorem dividedPower_identities_D_and_e_eq_gb (Q : PDPoly B) : ∃ D : ℕ → Q.P → Q.P,
    (∀ x, D 0 x = 1) ∧
    (∀ n x y, D n (x + y) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, D p.1 x * D p.2 y) ∧
    (∀ m n x, D m x * D n x = ((m + n).choose m : Q.P) * D (m + n) x) ∧
    (∀ n (c : B) x, D n (c • x) = algebraMap B Q.P c ^ n * D n x) ∧
    (∀ n K, K ≠ 0 → D n (Q.e K) = gb Q K n) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ℕ → B → PowerSeries Q.P, ∀ K b,
      F K b = PowerSeries.mk fun j => algebraMap B Q.P (b ^ j) * gb Q K j := ⟨_, fun _ _ => rfl⟩
  have F0 : ∀ K, F K 0 = 1 := by
    intro K
    ext j
    rw [hF, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    rcases j with _ | j
    · simp [gb_zero]
    · simp
  have Fadd : ∀ K, K ≠ 0 → ∀ a b, F K (a + b) = F K a * F K b := by
    intro K hK a b
    ext n
    rw [PowerSeries.coeff_mul]
    simp only [hF, PowerSeries.coeff_mk]
    have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        algebraMap B Q.P (a ^ p.1) * gb Q K p.1 * (algebraMap B Q.P (b ^ p.2) * gb Q K p.2) =
          algebraMap B Q.P (a ^ p.1 * b ^ p.2 * (n.choose p.1 : B)) * gb Q K n := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [mul_mul_mul_comm, gb_mul Q hK, hp]
      simp only [map_mul, map_natCast]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, add_pow,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have Fsc : ∀ K c b, F K (c * b) = PowerSeries.rescale (algebraMap B Q.P c) (F K b) := by
    intro K c b
    ext n
    rw [PowerSeries.coeff_rescale]
    simp only [hF, PowerSeries.coeff_mk, mul_pow, map_mul, map_pow]
    ring
  have Fexp : ∀ K, K ≠ 0 → ∀ b, IsExp (F K b) := by
    intro K hK b m n
    simp only [hF, PowerSeries.coeff_mk]
    rw [mul_mul_mul_comm, gb_mul Q hK, pow_add, map_mul]
    ring
  have exp1 : IsExp (1 : PowerSeries Q.P) := by
    intro m n
    simp only [PowerSeries.coeff_one]
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn]
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ → Q.P → PowerSeries Q.P, ∀ S x,
      E S x = ∏ k ∈ S, F (k + 1) (Q.e.repr x (k + 1)) := ⟨_, fun _ _ => rfl⟩
  have cover : ∀ x : Q.P, ∀ k, Q.e.repr x (k + 1) ≠ 0 →
      k ∈ Finset.range ((Q.e.repr x).support.sup id) := by
    intro x k hk
    have hmem : k + 1 ∈ (Q.e.repr x).support := Finsupp.mem_support_iff.mpr hk
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    exact Finset.mem_range.mpr (by omega)
  have Eind : ∀ x S T, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) →
      (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ T) → E S x = E T x := by
    intro x S T hS hT
    have mono : ∀ U V, U ⊆ V → (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ U) → E U x = E V x := by
      intro U V hUV hU
      rw [hE, hE]
      apply Finset.prod_subset hUV
      intro k _ hk
      have : Q.e.repr x (k + 1) = 0 := by
        by_contra h
        exact hk (hU k h)
      rw [this, F0]
    rw [mono S (S ∪ T) Finset.subset_union_left hS, mono T (S ∪ T) Finset.subset_union_right hT]
  have c0 : ∀ S x, PowerSeries.coeff 0 (E S x) = 1 := by
    intro S x
    rw [hE]
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      rw [Finset.prod_insert hk, PowerSeries.coeff_mul]
      simp [ih, hF, gb_zero]
  refine ⟨fun n x => PowerSeries.coeff n (E (Finset.range ((Q.e.repr x).support.sup id)) x),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact c0 _ x
  · intro n x y
    dsimp only
    obtain ⟨S, hxS, hyS, hxyS⟩ : ∃ S : Finset ℕ, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) ∧
        (∀ k, Q.e.repr y (k + 1) ≠ 0 → k ∈ S) ∧ (∀ k, Q.e.repr (x + y) (k + 1) ≠ 0 → k ∈ S) :=
      ⟨Finset.range ((Q.e.repr x).support.sup id) ∪ Finset.range ((Q.e.repr y).support.sup id) ∪
        Finset.range ((Q.e.repr (x + y)).support.sup id),
        fun k hk => Finset.mem_union_left _ (Finset.mem_union_left _ (cover x k hk)),
        fun k hk => Finset.mem_union_left _ (Finset.mem_union_right _ (cover y k hk)),
        fun k hk => Finset.mem_union_right _ (cover _ k hk)⟩
    rw [Eind x _ S (cover x) hxS, Eind y _ S (cover y) hyS, Eind (x + y) _ S (cover _) hxyS]
    have : E S (x + y) = E S x * E S y := by
      rw [hE, hE, hE, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [show Q.e.repr (x + y) = Q.e.repr x + Q.e.repr y from map_add _ _ _, Finsupp.add_apply,
        Fadd _ (Nat.succ_ne_zero k)]
    rw [this, PowerSeries.coeff_mul]
  · intro m n x
    dsimp only
    have : IsExp (E (Finset.range ((Q.e.repr x).support.sup id)) x) := by
      rw [hE]
      exact Finset.prod_induction _ IsExp (fun f g hf hg => hf.mul hg) exp1
        (fun k _ => Fexp _ (Nat.succ_ne_zero k) _)
    exact this m n
  · intro n c x
    dsimp only
    obtain ⟨S, hxS, hcS⟩ : ∃ S : Finset ℕ, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) ∧
        (∀ k, Q.e.repr (c • x) (k + 1) ≠ 0 → k ∈ S) :=
      ⟨Finset.range ((Q.e.repr x).support.sup id) ∪ Finset.range ((Q.e.repr (c • x)).support.sup id),
        fun k hk => Finset.mem_union_left _ (cover x k hk),
        fun k hk => Finset.mem_union_right _ (cover _ k hk)⟩
    rw [Eind x _ S (cover x) hxS, Eind (c • x) _ S (cover _) hcS]
    have : E S (c • x) = PowerSeries.rescale (algebraMap B Q.P c) (E S x) := by
      rw [hE, hE, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [show Q.e.repr (c • x) = c • Q.e.repr x from map_smul _ _ _, Finsupp.smul_apply, smul_eq_mul,
        Fsc]
    rw [this, PowerSeries.coeff_rescale]
  · intro n K hK
    dsimp only
    have hS : ∀ k, Q.e.repr (Q.e K) (k + 1) ≠ 0 →
        k ∈ Finset.range ((Q.e.repr (Q.e K)).support.sup id) ∪ {K - 1} :=
      fun k hk => Finset.mem_union_left _ (cover _ k hk)
    rw [Eind (Q.e K) _ _ (cover _) hS, hE, Finset.prod_eq_single (K - 1)]
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hK), Q.e.repr_self, Finsupp.single_eq_same, hF,
        PowerSeries.coeff_mk, one_pow, map_one, one_mul]
    · intro k _ hk
      rw [Q.e.repr_self, Finsupp.single_apply, if_neg (by omega), F0]
    · intro h
      exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self _)) h

theorem pre_aug (B : Type) [CommRing B] (Q : PDPoly B) : ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧
    ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  obtain ⟨D, h0, hadd, hexp, hsc, hgen⟩ := dividedPower_identities_D_and_e_eq_gb Q
  have hnat : ∀ (c : ℕ) (y : Q.P), (c : Q.P) * y = (c : B) • y := by
    intro c y
    rw [Algebra.smul_def, map_natCast]
  have hzero : ∀ n, n ≠ 0 → D n 0 = 0 := by
    intro n hn
    have := hsc n 0 0
    rw [zero_smul, map_zero, zero_pow hn, zero_mul] at this
    exact this
  have hmulgen : ∀ K, K ≠ 0 → ∀ (a : Q.P) n, D n (a * Q.e K) = a ^ n * D n (Q.e K) := by
    intro K hK a
    have ha : a ∈ Submodule.span B (Set.range Q.e) := by
      rw [Q.e.span_eq]
      trivial
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro n
      obtain ⟨M, hM, hpow⟩ := e_pow Q j n
      have key := num2 n j M hK hM
      have hr : (M : Q.P) * Q.e (n * j) * ((n.uniformBell K : Q.P) * Q.e (n * K)) =
          ((M * n.uniformBell K * (n * j + n * K).choose (n * j) : ℕ) : Q.P) * Q.e (n * j + n * K) := by
        rw [mul_mul_mul_comm, Q.e_mul]
        push_cast
        ring
      rw [Q.e_mul, hnat, hsc, hgen _ _ (by omega), hgen _ _ hK, hpow]
      unfold gb
      rw [hr, key, mul_add]
      simp only [map_natCast]
      push_cast
      ring
    | zero =>
      intro n
      rw [zero_mul]
      by_cases hn : n = 0
      · subst hn
        rw [h0, h0, pow_zero, one_mul]
      · rw [hzero n hn, zero_pow hn, zero_mul]
    | add a a' _ _ iha iha' =>
      intro n
      rw [add_mul, hadd, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hle : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      dsimp only
      rw [iha, iha', mul_mul_mul_comm, hexp, Nat.add_sub_cancel' hle]
      ring
    | smul c a _ iha =>
      intro n
      rw [smul_mul_assoc, hsc, iha, smul_pow, Algebra.smul_def, map_pow]
      ring
  have haug : ∀ x ∈ Q.aug, (∀ (a : Q.P) n, D n (a * x) = a ^ n * D n x) ∧ D 1 x = x ∧
      (∀ n, n ≠ 0 → D n x ∈ Q.aug) := by
    intro x hx
    have hx' : x ∈ Submodule.span Q.P (Set.range fun n => Q.e (n + 1)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨K, rfl⟩ := hy
      refine ⟨fun a n => hmulgen _ (by omega) a n, ?_, ?_⟩
      · rw [hgen 1 _ (by omega)]
        simp [gb, Nat.uniformBell_one_left]
      · intro n hn
        rw [hgen n _ (by omega)]
        unfold gb
        apply Ideal.mul_mem_left
        have hp : 0 < n * (K + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos K)
        obtain ⟨m, hm⟩ : ∃ m, n * (K + 1) = m + 1 := ⟨n * (K + 1) - 1, by omega⟩
        rw [hm]
        exact Q.e_succ_mem_aug m
    | zero =>
      refine ⟨fun a n => ?_, ?_, fun n hn => ?_⟩
      · rw [mul_zero]
        by_cases hn : n = 0
        · subst hn
          rw [h0, pow_zero, one_mul]
        · rw [hzero n hn, mul_zero]
      · exact hzero 1 one_ne_zero
      · rw [hzero n hn]
        exact Q.aug.zero_mem
    | add x y _ _ ihx ihy =>
      obtain ⟨mx, ox, memx⟩ := ihx
      obtain ⟨my, oy, memy⟩ := ihy
      refine ⟨fun a n => ?_, ?_, fun n hn => ?_⟩
      · rw [mul_add, hadd, hadd, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [mx, my, ← Finset.HasAntidiagonal.mem_antidiagonal.mp hp, pow_add]
        ring
      · rw [hadd]
        simp [Finset.Nat.sum_antidiagonal_succ, h0, ox, oy, add_comm]
      · rw [hadd]
        apply Ideal.sum_mem
        intro p hp
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        by_cases h1 : p.1 = 0
        · exact Ideal.mul_mem_left _ _ (memy _ (by omega))
        · exact Ideal.mul_mem_right _ _ (memx _ h1)
    | smul r x _ ih =>
      obtain ⟨mx, ox, memx⟩ := ih
      refine ⟨fun a n => ?_, ?_, fun n hn => ?_⟩
      · rw [smul_eq_mul, ← mul_assoc, mx, mx, mul_pow]
        ring
      · rw [smul_eq_mul, mx, ox, pow_one]
      · rw [smul_eq_mul, mx]
        exact Ideal.mul_mem_left _ _ (memx n hn)
  classical
  refine ⟨fun n x => if x ∈ Q.aug then D n x else 0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n x hx
    simp only [if_neg hx]
  · intro x hx
    simp only [if_pos hx, h0]
  · intro x hx
    simp only [if_pos hx]
    exact (haug x hx).2.1
  · intro n hn x hx
    simp only [if_pos hx]
    exact (haug x hx).2.2 n hn
  · intro n x hx y hy
    simp only [if_pos hx, if_pos hy, if_pos (Q.aug.add_mem hx hy)]
    exact hadd n x y
  · intro n a x hx
    simp only [if_pos hx, if_pos (Q.aug.mul_mem_left a hx)]
    exact (haug x hx).1 a n
  · intro m n x hx
    simp only [if_pos hx]
    exact hexp m n x
  · intro n k
    have hm : Q.e (k + 1) ∈ Q.aug := Q.e_succ_mem_aug k
    simp only [if_pos hm]
    rw [hgen n (k + 1) (by omega)]
    rfl

end FubiniStudyChowHeightFormula₂.Adr
