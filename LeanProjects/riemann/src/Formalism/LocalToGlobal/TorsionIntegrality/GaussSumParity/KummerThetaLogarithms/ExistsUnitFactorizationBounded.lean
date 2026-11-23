import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.RingAFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormRingALe

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)

namespace UnramifiedCompletion

variable (l : ℕ) [hl : Fact l.Prime]

lemma normL_lt_one : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := PadicComplex.norm_extends' l _
  have h2 : (((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by
    simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one

lemma castL_ne_zero : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero

variable {l}

lemma norm_ringA_le {x : ℂ_[l]} (hx : x ∈ ringA l) : ‖x‖ ≤ 1 := by
  first | exact UpperTheory.Reformulated.B.Qi27.norm_ringA_le .. | (apply UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi27.norm_ringA_le l hl x hx | exact @UpperTheory.Reformulated.B.Qi27.norm_ringA_le l hl x | exact @UpperTheory.Reformulated.B.Qi27.norm_ringA_le l hl | exact @UpperTheory.Reformulated.B.Qi27.norm_ringA_le l

lemma pow_pow_fix {M : Type*} [Monoid M] (x : M) (a : ℕ) (h : x ^ a = x) (k : ℕ) : x ^ (a ^ k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, h]

lemma castL_nonunit : ((l : ℕ) : ringA l) ∈ nonunits (ringA l) := by
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : (l : ℂ_[l]) * (y : ℂ_[l]) = 1 := by
    have := congrArg (fun t : ringA l => (t : ℂ_[l])) hy
    simpa using this
  have h2 : ‖(l : ℂ_[l])‖ * ‖(y : ℂ_[l])‖ = 1 := by rw [← norm_mul, h1, norm_one]
  have h3 : ‖(l : ℂ_[l])‖ * ‖(y : ℂ_[l])‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (normL_lt_one l) (norm_ringA_le y.2)
  exact absurd h2 h3.ne

lemma exists_period {x : ℂ_[l]} (hx : x ∈ ringA l) :
    ∃ f : ℕ, 0 < f ∧
      (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ringA l)}) ⟨x, hx⟩) ^ (l ^ f)
        = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ringA l)}) ⟨x, hx⟩ := by
  have : CharP (ringA l ⧸ Ideal.span {((l : ℕ) : ringA l)}) l := CharP.quotient _ l castL_nonunit
  set mk := Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ringA l)}) with hmk
  have key : ∀ (a b : ringA l ⧸ Ideal.span {((l : ℕ) : ringA l)}) (f g : ℕ), a ^ (l ^ f) = a →
      b ^ (l ^ g) = b → a ^ (l ^ (f * g)) = a ∧ b ^ (l ^ (f * g)) = b := by
    intro a b f g ha hb
    constructor
    · rw [pow_mul]; exact pow_pow_fix a _ ha g
    · rw [mul_comm, pow_mul]; exact pow_pow_fix b _ hb f
  refine Subring.closure_induction
    (p := fun x hx => ∃ f : ℕ, 0 < f ∧ (mk ⟨x, hx⟩) ^ (l ^ f) = mk ⟨x, hx⟩) ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro z hz
    obtain ⟨n, hn, hln, h⟩ := hz
    have hcop : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl.out).2 hln
    refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
    have h1 : l ^ n.totient ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop
    have h2 : z ^ (l ^ n.totient) = z := by
      have h3 : z ^ (l ^ n.totient) = z ^ 1 := by
        rw [← Nat.div_add_mod (l ^ n.totient) n, ← Nat.div_add_mod 1 n, h1, pow_add, pow_add, pow_mul,
          pow_mul, h]
        simp
      simpa using h3
    rw [← map_pow]
    congr 1
    exact Subtype.ext h2
  · exact ⟨1, one_pos, by
      have : (⟨0, zero_mem _⟩ : ringA l) = 0 := rfl
      rw [this, map_zero, zero_pow (pow_ne_zero _ hl.out.ne_zero)]⟩
  · exact ⟨1, one_pos, by
      have : (⟨1, one_mem _⟩ : ringA l) = 1 := rfl
      rw [this, map_one, one_pow]⟩
  · rintro x y hx hy ⟨f, hf, h1⟩ ⟨g, hg, h2⟩
    obtain ⟨k1, k2⟩ := key _ _ f g h1 h2
    refine ⟨f * g, Nat.mul_pos hf hg, ?_⟩
    have : (⟨x + y, add_mem hx hy⟩ : ringA l) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, add_pow_char_pow, k1, k2]
  · rintro x hx ⟨f, hf, h1⟩
    refine ⟨f, hf, ?_⟩
    have : (⟨-x, neg_mem hx⟩ : ringA l) = -⟨x, hx⟩ := rfl
    rw [this, map_neg]
    have h0 := map_neg (iterateFrobenius (ringA l ⧸ Ideal.span {((l : ℕ) : ringA l)}) l f) (mk ⟨x, hx⟩)
    rw [iterateFrobenius_def, iterateFrobenius_def, h1] at h0
    exact h0
  · rintro x y hx hy ⟨f, hf, h1⟩ ⟨g, hg, h2⟩
    obtain ⟨k1, k2⟩ := key _ _ f g h1 h2
    refine ⟨f * g, Nat.mul_pos hf hg, ?_⟩
    have : (⟨x * y, mul_mem hx hy⟩ : ringA l) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, mul_pow, k1, k2]

end UnramifiedCompletion

open UnramifiedCompletion

theorem ring_a_facts : RingAFacts := by
  intro l hl
  refine ⟨fun x hx => norm_ringA_le hx, ?_⟩
  intro x hx
  obtain ⟨f, hf, h⟩ := exists_period hx
  refine ⟨f, hf, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, c.2, ?_⟩
  have := congrArg (fun t : ringA l => (t : ℂ_[l])) hc
  simpa using this

namespace UnramifiedCompletion

variable {l : ℕ} [hl : Fact l.Prime]

lemma ringA_le_ringB : ringA l ≤ ringB l := Subring.le_topologicalClosure _

lemma isClosed_ringB : IsClosed (ringB l : Set ℂ_[l]) := Subring.isClosed_topologicalClosure _

lemma norm_ringB_le {x : ℂ_[l]} (hx : x ∈ ringB l) : ‖x‖ ≤ 1 := by
  have h : closure (ringA l : Set ℂ_[l]) ⊆ {x | ‖x‖ ≤ 1} :=
    closure_minimal (fun x hx => norm_ringA_le hx) (isClosed_le continuous_norm continuous_const)
  exact h hx

lemma castL_mem_ringB : (l : ℂ_[l]) ∈ ringB l := natCast_mem _ l

lemma geom_mem {w : ℂ_[l]} (hw : w ∈ ringB l) (h : ‖w‖ < 1) : (1 - w)⁻¹ ∈ ringB l := by
  have h1 := (hasSum_geometric_of_norm_lt_one h).tendsto_sum_nat
  exact isClosed_ringB.mem_of_tendsto h1
    (Eventually.of_forall fun n => sum_mem fun i _ => pow_mem hw i)

lemma exists_pow_eq (f : ℕ) (hf : 0 < f) : ∃ N : ℕ, l ^ f = N + 2 := by
  have h2 : 2 ≤ l ^ f := hl.out.two_le.trans (Nat.le_self_pow hf.ne' l)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h2
  exact ⟨k, by omega⟩

def PerA (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ x ∈ ringA l, ∃ f : ℕ, 0 < f ∧ ∃ y ∈ ringA l, x ^ (l ^ f) - x = (l : ℂ_[l]) * y

lemma div_ringA (hA : PerA l) {x : ℂ_[l]} (hx : x ∈ ringA l) (h : ‖x‖ < 1) :
    ∃ y ∈ ringB l, x = (l : ℂ_[l]) * y := by
  obtain ⟨f, hf, y, hy, e⟩ := hA x hx
  obtain ⟨N, hN⟩ := exists_pow_eq (l := l) f hf
  have hxN : ‖x ^ (N + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h (Nat.succ_ne_zero _)
  have hne : 1 - x ^ (N + 1) ≠ 0 := by
    intro h0
    have h1 : x ^ (N + 1) = 1 := (sub_eq_zero.1 h0).symm
    rw [h1, norm_one] at hxN
    exact lt_irrefl _ hxN
  refine ⟨-y * (1 - x ^ (N + 1))⁻¹,
    mul_mem (neg_mem (ringA_le_ringB hy)) (geom_mem (pow_mem (ringA_le_ringB hx) _) hxN), ?_⟩
  have e2 : x * (1 - x ^ (N + 1)) = (l : ℂ_[l]) * (-y) := by
    rw [hN] at e
    linear_combination -e
  rw [← mul_assoc, ← e2, mul_assoc, mul_inv_cancel₀ hne, mul_one]

lemma div_ringB (hA : PerA l) {x : ℂ_[l]} (hx : x ∈ ringB l) (h : ‖x‖ < 1) :
    ∃ y ∈ ringB l, x = (l : ℂ_[l]) * y := by
  obtain ⟨u, hu, hlim⟩ :=
    mem_closure_iff_seq_limit.1 (show x ∈ closure (ringA l : Set ℂ_[l]) from hx)
  have hev : ∀ᶠ n in atTop, ‖u n‖ < 1 := (hlim.norm).eventually_lt_const h
  have hlim2 : Tendsto (fun n => (l : ℂ_[l])⁻¹ * u n) atTop (𝓝 ((l : ℂ_[l])⁻¹ * x)) :=
    hlim.const_mul _
  refine ⟨(l : ℂ_[l])⁻¹ * x, isClosed_ringB.mem_of_tendsto hlim2 (hev.mono fun n hn => ?_),
    by rw [mul_inv_cancel_left₀ (castL_ne_zero l)]⟩
  obtain ⟨y, hy, e⟩ := div_ringA hA (hu n) hn
  rw [e, inv_mul_cancel_left₀ (castL_ne_zero l)]
  exact hy

lemma inv_ringA (hA : PerA l) {u : ℂ_[l]} (hu : u ∈ ringA l) (h : ‖u‖ = 1) : u⁻¹ ∈ ringB l := by
  obtain ⟨f, hf, y, hy, e⟩ := hA u hu
  obtain ⟨N, hN⟩ := exists_pow_eq (l := l) f hf
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
  have e2 : u * (1 - u ^ (N + 1)) = (l : ℂ_[l]) * (-y) := by
    rw [hN] at e
    linear_combination -e
  have hw : ‖1 - u ^ (N + 1)‖ < 1 := by
    have h1 := congrArg norm e2
    rw [norm_mul, norm_mul, h, one_mul, norm_neg] at h1
    rw [h1]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (normL_lt_one l) (norm_ringA_le hy)
  have hB : 1 - u ^ (N + 1) ∈ ringB l := sub_mem (one_mem _) (pow_mem (ringA_le_ringB hu) _)
  have h3 := geom_mem hB hw
  rw [sub_sub_cancel] at h3
  have h4 : u⁻¹ = u ^ N * (u ^ (N + 1))⁻¹ := by
    rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu0), one_mul]
  rw [h4]
  exact mul_mem (pow_mem (ringA_le_ringB hu) _) h3

lemma inv_ringB (hA : PerA l) {u : ℂ_[l]} (hu : u ∈ ringB l) (h : ‖u‖ = 1) : u⁻¹ ∈ ringB l := by
  obtain ⟨u0, hu0, hd⟩ :=
    Metric.mem_closure_iff.1 (show u ∈ closure (ringA l : Set ℂ_[l]) from hu) 1 one_pos
  rw [dist_eq_norm] at hd
  have hn : ‖u0‖ = 1 := by
    refine le_antisymm (norm_ringA_le hu0) ?_
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ‖u‖ ≤ max ‖u - u0‖ ‖u0‖ := by
      simpa using IsUltrametricDist.norm_add_le_max (u - u0) u0
    rw [h] at h1
    exact absurd h1 (not_le.2 (max_lt hd hlt))
  have hne : u0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  have hi := inv_ringA hA hu0 hn
  have hwB : u0⁻¹ * (u0 - u) ∈ ringB l := mul_mem hi (sub_mem (ringA_le_ringB hu0) hu)
  have hw : ‖u0⁻¹ * (u0 - u)‖ < 1 := by
    rw [norm_mul, norm_inv, hn, inv_one, one_mul, norm_sub_rev]; exact hd
  have e : u = u0 * (1 - u0⁻¹ * (u0 - u)) := by
    rw [mul_sub, mul_one, mul_inv_cancel_left₀ hne, sub_sub_cancel]
  have h5 := mul_mem hi (geom_mem hwB hw)
  rw [← mul_inv, ← e] at h5
  exact h5

def DivB (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ x ∈ ringB l, ‖x‖ < 1 → ∃ y ∈ ringB l, x = (l : ℂ_[l]) * y

lemma exists_unit_factorization_bounded (hdiv : DivB l) : ∀ n : ℕ, ∀ x ∈ ringB l, ‖(l : ℂ_[l])‖ ^ n < ‖x‖ →
    ∃ k : ℕ, ∃ u ∈ ringB l, ‖u‖ = 1 ∧ x = (l : ℂ_[l]) ^ k * u := by
  intro n
  induction n with
  | zero =>
    intro x hx h
    rw [pow_zero] at h
    exact absurd (norm_ringB_le hx) (not_le.2 h)
  | succ n ih =>
    intro x hx h
    rcases (norm_ringB_le hx).lt_or_eq with h1 | h1
    · obtain ⟨y, hy, e⟩ := hdiv x hx h1
      have h2 : ‖(l : ℂ_[l])‖ ^ n < ‖y‖ := by
        rw [e, norm_mul, pow_succ, mul_comm] at h
        exact lt_of_mul_lt_mul_left h (norm_nonneg _)
      obtain ⟨k, u, hu, hu1, e2⟩ := ih y hy h2
      exact ⟨k + 1, u, hu, hu1, by rw [e, e2, pow_succ]; ring⟩
    · exact ⟨0, x, hx, h1, by simp⟩

lemma exists_unit (hdiv : DivB l) {x : ℂ_[l]} (hx : x ∈ ringB l) (h0 : x ≠ 0) :
    ∃ k : ℕ, ∃ u ∈ ringB l, ‖u‖ = 1 ∧ x = (l : ℂ_[l]) ^ k * u := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 h0) (normL_lt_one l)
  exact exists_unit_factorization_bounded hdiv n x hx hn

lemma mem_of_pow_mul (hdiv : DivB l) : ∀ (k : ℕ) (x : ℂ_[l]), ‖x‖ ≤ 1 →
    (l : ℂ_[l]) ^ k * x ∈ ringB l → x ∈ ringB l := by
  intro k
  induction k with
  | zero => intro x _ h; simpa using h
  | succ k ih =>
    intro x hx h
    have h1 : ‖(l : ℂ_[l]) ^ (k + 1) * x‖ < 1 := by
      rw [norm_mul, norm_pow]
      exact mul_lt_one_of_nonneg_of_lt_one_left (pow_nonneg (norm_nonneg _) _)
        (pow_lt_one₀ (norm_nonneg _) (normL_lt_one l) (Nat.succ_ne_zero _)) hx
    obtain ⟨y, hy, e⟩ := hdiv _ h h1
    refine ih x hx ?_
    have e2 : (l : ℂ_[l]) ^ k * x = y := by
      apply mul_left_cancel₀ (castL_ne_zero l)
      rw [← e, pow_succ]; ring
    rw [e2]; exact hy

def fracS (hdiv : DivB l) (hinv : ∀ x ∈ ringB l, ‖x‖ = 1 → x⁻¹ ∈ ringB l) : Subfield ℂ_[l] where
  carrier := {x | ∃ k : ℕ, (l : ℂ_[l]) ^ k * x ∈ ringB l}
  mul_mem' := by
    rintro a b ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨j + k, ?_⟩
    have h := mul_mem hj hk
    convert h using 1
    ring
  one_mem' := ⟨0, by simp [one_mem]⟩
  add_mem' := by
    rintro a b ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨j + k, ?_⟩
    have h := add_mem (mul_mem (pow_mem castL_mem_ringB k) hj) (mul_mem (pow_mem castL_mem_ringB j) hk)
    convert h using 1
    ring
  zero_mem' := ⟨0, by simp [zero_mem]⟩
  neg_mem' := by
    rintro a ⟨j, hj⟩
    exact ⟨j, by rw [mul_neg]; exact neg_mem hj⟩
  inv_mem' := by
    rintro a ⟨j, hj⟩
    by_cases h0 : a = 0
    · exact ⟨0, by simp [h0, zero_mem]⟩
    obtain ⟨k, u, hu, hu1, e⟩ :=
      exists_unit hdiv hj (mul_ne_zero (pow_ne_zero _ (castL_ne_zero l)) h0)
    have hu0 : u ≠ 0 := by
      intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
    refine ⟨k, ?_⟩
    have e2 : (l : ℂ_[l]) ^ k * a⁻¹ = (l : ℂ_[l]) ^ j * u⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul₀ h0, mul_assoc, mul_comm u⁻¹ a, ← mul_assoc, e, mul_assoc,
        mul_inv_cancel₀ hu0, mul_one]
    rw [e2]
    exact mul_mem (pow_mem castL_mem_ringB j) (hinv u hu hu1)

lemma ringB_le_Kur {x : ℂ_[l]} (hx : x ∈ ringB l) : x ∈ MaximalUnramifiedExtension l := by
  have h1 : ringA l ≤ (MaximalUnramifiedExtension l).toSubring :=
    Subring.closure_le.2 fun z hz => Subfield.le_topologicalClosure _ (Subfield.subset_closure hz)
  exact Subring.topologicalClosure_minimal _ h1 (Subfield.isClosed_topologicalClosure _) hx

end UnramifiedCompletion

theorem KurIntegers_of : RingAFacts → KurIntegers := by
  intro hA l hl
  have hA2 : PerA l := (hA l).2
  have hdiv : DivB l := fun x hx h => div_ringB hA2 hx h
  have hinv : ∀ x ∈ ringB l, ‖x‖ = 1 → x⁻¹ ∈ ringB l := fun x hx h => inv_ringB hA2 hx h
  refine ⟨fun x => ⟨fun hx => ⟨ringB_le_Kur hx, norm_ringB_le hx⟩, ?_⟩, hdiv, hinv⟩
  rintro ⟨hK, h1⟩
  have hF : Subfield.closure (muPrime l) ≤ fracS hdiv hinv :=
    Subfield.closure_le.2 fun z hz =>
      ⟨0, by simpa using ringA_le_ringB (Subring.subset_closure hz)⟩
  have h2 : x ∈ closure (ringB l : Set ℂ_[l]) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨x0, hx0, hd⟩ := Metric.mem_closure_iff.1
      (show x ∈ closure ((Subfield.closure (muPrime l) : Subfield ℂ_[l]) : Set ℂ_[l]) from hK)
      (min ε 1) (lt_min hε one_pos)
    refine ⟨x0, ?_, hd.trans_le (min_le_left _ _)⟩
    obtain ⟨k, hk⟩ := hF hx0
    have hn : ‖x0‖ ≤ 1 := by
      have h3 : ‖x0‖ ≤ max ‖x0 - x‖ ‖x‖ := by
        simpa using IsUltrametricDist.norm_add_le_max (x0 - x) x
      refine h3.trans (max_le ?_ h1)
      rw [← dist_eq_norm, dist_comm]
      exact (hd.trans_le (min_le_right _ _)).le
    exact mem_of_pow_mul hdiv k x0 hn hk
  rwa [isClosed_ringB.closure_eq] at h2

theorem KurUnram_of : KurIntegers → KurUnram := by
  intro hK l hl a ha h0
  obtain ⟨h1, hdiv, -⟩ := hK l
  have key : ∀ x ∈ ringB l, x ≠ 0 → ∃ k : ℕ, ‖x‖ = ‖(l : ℂ_[l])‖ ^ k := by
    intro x hx hx0
    obtain ⟨k, u, _, hu1, e⟩ := exists_unit hdiv hx hx0
    exact ⟨k, by rw [e, norm_mul, norm_pow, hu1, mul_one]⟩
  rcases le_total ‖a‖ 1 with h | h
  · obtain ⟨k, hk⟩ := key a ((h1 a).2 ⟨ha, h⟩) h0
    exact ⟨k, by rw [hk, zpow_natCast]⟩
  · have hi : ‖a⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h
    obtain ⟨k, hk⟩ := key a⁻¹ ((h1 _).2 ⟨inv_mem ha, hi⟩) (inv_ne_zero h0)
    exact ⟨-k, by rw [zpow_neg, zpow_natCast, ← hk, norm_inv, inv_inv]⟩

theorem unramified_completion_roots : KurRoots := by
  intro l hl n hn hln
  have : NeZero (n : ℂ_[l]) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] n
  have hmem : z ∈ MaximalUnramifiedExtension l :=
    Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hln, hz.pow_eq_one⟩)
  refine ⟨⟨z, hmem⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := (MaximalUnramifiedExtension l).subtype) hz Subtype.val_injective

theorem unramified_completion_complete : KurComplete := by
  intro l hl
  exact (Subfield.isClosed_topologicalClosure _).completeSpace_coe

end Formalism.L2.Th1.D
