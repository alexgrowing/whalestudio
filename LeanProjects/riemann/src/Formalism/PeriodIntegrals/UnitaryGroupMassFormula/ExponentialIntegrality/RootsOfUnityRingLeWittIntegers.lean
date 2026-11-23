import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Development

noncomputable section

namespace PI.ExpIntWProof.Key

abbrev S0 (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}

lemma rootsOfUnityRing_le_wittIntegers (p : ℕ) [Fact p.Prime] : S0 p ≤ Wp p := Subring.le_topologicalClosure _

lemma isClosed_Wp (p : ℕ) [Fact p.Prime] : IsClosed (Wp p : Set ℂ_[p]) :=
  Subring.isClosed_topologicalClosure _

lemma pow_pow_mul {R : Type*} [CommRing R] (a : R) (p f : ℕ) (h : a ^ p ^ f = a) :
    ∀ k : ℕ, a ^ p ^ (f * k) = a
  | 0 => by simp
  | k + 1 => by
      rw [Nat.mul_succ, pow_add, pow_mul, pow_pow_mul a p f h k, h]

def Fx {R : Type*} [CommRing R] (p : ℕ) (a : R) : Prop := ∃ f : ℕ, 0 < f ∧ a ^ p ^ f = a

section Frob

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

lemma Fx.common {a b : R} (ha : Fx p a) (hb : Fx p b) :
    ∃ f : ℕ, 0 < f ∧ a ^ p ^ f = a ∧ b ^ p ^ f = b := by
  obtain ⟨f, hf, hfa⟩ := ha
  obtain ⟨g, hg, hgb⟩ := hb
  refine ⟨f * g, Nat.mul_pos hf hg, pow_pow_mul a p f hfa g, ?_⟩
  rw [mul_comm]; exact pow_pow_mul b p g hgb f

lemma Fx.add {a b : R} (ha : Fx p a) (hb : Fx p b) : Fx p (a + b) := by
  obtain ⟨f, hf, h1, h2⟩ := Fx.common p ha hb
  exact ⟨f, hf, by rw [add_pow_char_pow, h1, h2]⟩

lemma Fx.mul {a b : R} (ha : Fx p a) (hb : Fx p b) : Fx p (a * b) := by
  obtain ⟨f, hf, h1, h2⟩ := Fx.common p ha hb
  exact ⟨f, hf, by rw [mul_pow, h1, h2]⟩

lemma Fx.neg {a : R} (ha : Fx p a) : Fx p (-a) := by
  obtain ⟨f, hf, h1⟩ := ha
  have : ExpChar R p := ExpChar.prime hp.out
  refine ⟨f, hf, ?_⟩
  rw [neg_eq_neg_one_mul, mul_pow, neg_one_pow_expChar_pow, h1]

end Frob

variable {p : ℕ} [hp : Fact p.Prime]

lemma root_frob {x : ℂ_[p]} {n : ℕ} (_hn : 0 < n) (hc : Nat.Coprime n p) (hx : x ^ n = 1) :
    x ^ p ^ Nat.totient n = x := by
  have hred : ∀ a : ℕ, x ^ a = x ^ (a % n) := fun a => by
    conv_lhs => rw [← Nat.div_add_mod a n]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  have hmod : p ^ Nat.totient n % n = 1 % n := Nat.ModEq.pow_totient hc.symm
  rw [hred, hmod, ← hred, pow_one]

theorem frob_congr (y : ℂ_[p]) (hy : y ∈ S0 p) :
    ∃ f : ℕ, 0 < f ∧ ∃ z ∈ S0 p, y ^ p ^ f - y = (p : ℂ_[p]) * z := by
  classical
  let I : Ideal (S0 p) := Ideal.span {((p : ℕ) : S0 p)}
  suffices H : ∀ a : S0 p, Fx p (Ideal.Quotient.mk I a) by
    obtain ⟨f, hf, h⟩ := H ⟨y, hy⟩
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨f, hf, z, z.2, ?_⟩
    have := congrArg Subtype.val hz
    simpa using this
  have hp0 : ((p : ℕ) : S0 p ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I) p]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  rcases (Nat.dvd_prime hp.out).1 (ringChar.dvd hp0) with h1 | h1
  · have : CharP (S0 p ⧸ I) 1 := ringChar.of_eq h1
    have := CharP.CharOne.subsingleton (R := S0 p ⧸ I)
    exact fun a => ⟨1, one_pos, Subsingleton.elim _ _⟩
  · have : CharP (S0 p ⧸ I) p := ringChar.of_eq h1
    rintro ⟨y, hy⟩
    induction hy using Subring.closure_induction with
    | mem x hx =>
        obtain ⟨n, hn, hc, hxn⟩ := hx
        refine ⟨Nat.totient n, Nat.totient_pos.2 hn, ?_⟩
        rw [← map_pow]
        congr 1
        exact Subtype.ext (by simpa using root_frob hn hc hxn)
    | zero => exact ⟨1, one_pos, by rw [show (⟨0, _⟩ : S0 p) = 0 from rfl, map_zero, zero_pow (pow_ne_zero _ hp.out.ne_zero)]⟩
    | one => exact ⟨1, one_pos, by rw [show (⟨1, _⟩ : S0 p) = 1 from rfl, map_one, one_pow]⟩
    | add x y hx hy ihx ihy =>
        rw [show (⟨x + y, _⟩ : S0 p) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]
        exact Fx.add p ihx ihy
    | neg x hx ih =>
        rw [show (⟨-x, _⟩ : S0 p) = -⟨x, hx⟩ from rfl, map_neg]
        exact Fx.neg p ih
    | mul x y hx hy ihx ihy =>
        rw [show (⟨x * y, _⟩ : S0 p) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
        exact Fx.mul p ihx ihy

lemma inv_one_sub_mem {ξ : ℂ_[p]} (hξ : ξ ∈ Wp p) (h : ‖ξ‖ < 1) : (1 - ξ)⁻¹ ∈ Wp p := by
  have hs := (hasSum_geometric_of_norm_lt_one h).tendsto_sum_nat
  refine (isClosed_Wp p).mem_of_tendsto hs (Filter.Eventually.of_forall fun n => ?_)
  exact Subring.sum_mem _ fun i _ => Subring.pow_mem _ hξ i

lemma natp_ne_zero : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero

theorem div_p_mem_of_S {y : ℂ_[p]} (hy : y ∈ S0 p) (h : ‖y‖ < 1) : y / p ∈ Wp p := by
  obtain ⟨f, hf, z, hz, he⟩ := frob_congr y hy
  set q := p ^ f with hqdef
  have hpq : p ≤ q := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.out.pos hf
  have h2 : 2 ≤ q := le_trans hp.out.two_le hpq
  set ξ := y ^ (q - 1) with hξdef
  have hξW : ξ ∈ Wp p := rootsOfUnityRing_le_wittIntegers p (Subring.pow_mem _ hy _)
  have hξn : ‖ξ‖ < 1 := by
    rw [hξdef, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h (by omega)
  have hne : (1 - ξ) ≠ 0 := by
    intro h0
    have : ξ = 1 := (sub_eq_zero.1 h0).symm
    rw [this, norm_one] at hξn; exact lt_irrefl _ hξn
  have hyq : y * ξ = y ^ q := by
    rw [hξdef, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]
  have h1 : y * (1 - ξ) = -((p : ℂ_[p]) * z) := by
    rw [mul_sub, mul_one, hyq, ← he]; ring
  have hval : y / p = -z * (1 - ξ)⁻¹ := by
    have hp0 := natp_ne_zero (p := p)
    rw [div_eq_iff hp0]
    calc y = y * (1 - ξ) * (1 - ξ)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
      _ = -z * (1 - ξ)⁻¹ * p := by rw [h1]; ring
  rw [hval]
  exact Subring.mul_mem _ (Subring.neg_mem _ (rootsOfUnityRing_le_wittIntegers p hz)) (inv_one_sub_mem hξW hξn)

end PI.ExpIntWProof.Key

namespace PI.ExpIntWProof

open Key in

theorem keyW : KeyW := by
  intro p _ x hx h
  rw [← SetLike.mem_coe, ← (isClosed_Wp p).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hpn : (0 : ℝ) < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 natp_ne_zero
  have hxS : x ∈ closure (S0 p : Set ℂ_[p]) := hx
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.1 hxS (min (ε * ‖(p : ℂ_[p])‖) (1 - ‖x‖))
    (lt_min (mul_pos hε hpn) (by linarith))
  rw [dist_eq_norm] at hxy
  refine ⟨y / p, div_p_mem_of_S hyS ?_, ?_⟩
  · calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
      _ < ‖x‖ + (1 - ‖x‖) := by linarith [min_le_right (ε * ‖(p : ℂ_[p])‖) (1 - ‖x‖)]
      _ = 1 := by ring
  · rw [dist_eq_norm, ← sub_div, norm_div, div_lt_iff₀ hpn]
    exact lt_of_lt_of_le hxy (min_le_left _ _)

end PI.ExpIntWProof

end
