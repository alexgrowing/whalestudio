import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per Ideal Finset

namespace GlobalTheory.Per.AinfComplete

section General

variable {A : Type*} [CommRing A]

def Summ (y : A) : Prop :=
  ∀ b : ℕ → A, ∃ L, ∀ n, L - ∑ i ∈ range n, y ^ i * b i ∈ span {y ^ n}

def Tails (y : A) : Prop := ∀ b : ℕ → A, ∃ t : ℕ → A, ∀ n, b n = t n - y * t (n + 1)

theorem summ_of_precomplete (y : A) [h : IsPrecomplete (span {y}) A] : Summ y := by
  intro b
  have hC : ∀ m n, m ≤ n →
      ∑ i ∈ range m, y ^ i * b i - ∑ i ∈ range n, y ^ i * b i ∈ span {y ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [sum_range_succ, ← sub_sub]
      exact sub_mem ih (mem_span_singleton.2 (Dvd.dvd.mul_right (pow_dvd_pow y hmn) _))
  obtain ⟨L, hL⟩ := h.prec' (fun n => ∑ i ∈ range n, y ^ i * b i) (by
    intro m n hmn
    simp only [span_singleton_pow, smul_eq_mul, mul_top, SModEq.sub_mem]
    exact hC m n hmn)
  refine ⟨L, fun n => ?_⟩
  have hn := hL n
  simp only [span_singleton_pow, smul_eq_mul, mul_top, SModEq.sub_mem] at hn
  rw [← neg_sub]
  exact neg_mem hn

theorem summ_of_tails {y : A} (h : Tails y) : Summ y := by
  intro b
  obtain ⟨t, ht⟩ := h b
  refine ⟨t 0, fun n => ?_⟩
  have : t 0 - ∑ i ∈ range n, y ^ i * b i = y ^ n * t n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ← sub_sub, ih, ht n]; ring
  rw [this]
  exact mul_mem_right _ _ (mem_span_singleton_self _)

theorem precomplete_of_summ {y : A} (h : Summ y) : IsPrecomplete (span {y}) A := by
  refine ⟨fun f hf => ?_⟩
  simp only [span_singleton_pow, smul_eq_mul, mul_top, SModEq.sub_mem] at hf ⊢
  have h1 : ∀ n, ∃ b, b * y ^ n = f n - f (n + 1) := fun n =>
    mem_span_singleton'.1 (hf (Nat.le_succ n))
  choose b hb using h1
  obtain ⟨L, hL⟩ := h b
  refine ⟨f 0 - L, fun n => ?_⟩
  have : ∑ i ∈ range n, y ^ i * b i = f 0 - f n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; linear_combination hb n
  have h2 := hL n
  rw [this] at h2
  convert h2 using 1
  ring

theorem pair_pow_le (p y : A) (n : ℕ) : span {p, y} ^ (2 * n) ≤ span {p ^ n, y ^ n} := by
  rw [span_insert, span_insert, ← span_singleton_pow, ← span_singleton_pow, two_mul]
  exact sup_pow_add_le_pow_sup_pow

theorem le_pair_pow (p y : A) (n : ℕ) : span {p ^ n, y ^ n} ≤ span {p, y} ^ n := by
  rw [span_le]
  rintro x (rfl | rfl)
  · exact pow_mem_pow (subset_span (by simp)) n
  · exact pow_mem_pow (subset_span (by simp)) n

theorem precomplete_pair {p y : A} (hp : Summ p) (hy : Summ y) :
    IsPrecomplete (span {p, y}) A := by
  refine ⟨fun f hf => ?_⟩
  simp only [smul_eq_mul, mul_top, SModEq.sub_mem] at hf ⊢
  have h1 : ∀ n, ∃ a b, a * p ^ n + b * y ^ n = f (2 * n) - f (2 * (n + 1)) := fun n =>
    mem_span_pair.1 (pair_pow_le p y n (hf (by omega)))
  choose a b hab using h1
  obtain ⟨L, hL⟩ := hp a
  obtain ⟨M, hM⟩ := hy b
  refine ⟨f 0 - L - M, fun n => ?_⟩
  have : ∑ i ∈ range n, p ^ i * a i + ∑ i ∈ range n, y ^ i * b i = f 0 - f (2 * n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, sum_range_succ]; linear_combination hab n + ih
  have h2 : L - ∑ i ∈ range n, p ^ i * a i ∈ span {p, y} ^ n :=
    le_pair_pow p y n (span_mono (by simp) (hL n))
  have h3 : M - ∑ i ∈ range n, y ^ i * b i ∈ span {p, y} ^ n :=
    le_pair_pow p y n (span_mono (by simp) (hM n))
  have h4 : f n - f (2 * n) ∈ span {p, y} ^ n := hf (by omega)
  convert add_mem (add_mem h2 h3) h4 using 1
  linear_combination this

theorem eq_zero_of_haus (p : A) [h : IsHausdorff (span {p}) A] (x : A)
    (hx : ∀ n, x ∈ span {p ^ n}) : x = 0 := by
  refine h.haus' x fun n => ?_
  simp only [span_singleton_pow, smul_eq_mul, mul_top, SModEq.zero]
  exact hx n

theorem tails_of_mod (p y : A) [IsAdicComplete (span {p}) A]
    (h : ∀ b : ℕ → A, ∃ t c : ℕ → A, ∀ n, b n = t n - y * t (n + 1) + p * c n) : Tails y := by
  choose τ γ hτ using h
  intro b
  have hs := summ_of_precomplete p
  choose T hT using fun n => hs fun k => τ (γ^[k] b) n
  refine ⟨T, fun n => ?_⟩
  have key : ∀ k, b n = ∑ i ∈ range k, p ^ i * τ (γ^[i] b) n -
      y * ∑ i ∈ range k, p ^ i * τ (γ^[i] b) (n + 1) + p ^ k * γ^[k] b n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, sum_range_succ, Function.iterate_succ_apply']
      linear_combination ih + p ^ k * hτ (γ^[k] b) n
  rw [← sub_eq_zero]
  refine eq_zero_of_haus p _ fun k => ?_
  convert add_mem (sub_mem (mul_mem_left _ y (hT (n + 1) k)) (hT n k))
    (mul_mem_right (γ^[k] b n) _ (mem_span_singleton_self (p ^ k))) using 1
  linear_combination key k

theorem hausdorff_pair {R : Type*} [CommRing R] [IsDomain R] (π : A →+* R) (p y : A)
    [IsHausdorff (span {p}) A] (hker : RingHom.ker π = span {p})
    (hreg : ∀ x, x * p = 0 → x = 0) (hR : ∀ x : R, (∀ n, π y ^ n ∣ x) → x = 0) :
    IsHausdorff (span {p, y}) A := by
  have hπp : π p = 0 := by
    rw [← RingHom.mem_ker, hker]; exact mem_span_singleton_self _
  by_cases hy : π y = 0
  · have hy' : y ∈ span {p} := hker ▸ hy
    have : span {p, y} = span {p} := by
      rw [span_insert, sup_eq_left, span_singleton_le_iff_mem]; exact hy'
    rw [this]; infer_instance
  have step : ∀ x : A, (∀ n, x ∈ span {p ^ n, y ^ n}) →
      ∃ x', x = p * x' ∧ ∀ n, x' ∈ span {p ^ n, y ^ n} := by
    intro x hx
    have h0 : π x = 0 := by
      refine hR _ fun n => ?_
      obtain ⟨a, b, rfl⟩ := mem_span_pair.1 (hx (n + 1))
      simp only [map_add, map_mul, map_pow, hπp, pow_succ, mul_zero, zero_add]
      exact ⟨π b * π y, by ring⟩
    obtain ⟨x', hx'⟩ := mem_span_singleton'.1 (hker ▸ h0 : x ∈ span {p})
    refine ⟨x', by rw [← hx', mul_comm], fun n => ?_⟩
    obtain ⟨a, b, hab⟩ := mem_span_pair.1 (hx (n + 1))
    have h1 : π b = 0 := by
      rw [← hab] at h0
      simp only [map_add, map_mul, map_pow, hπp, pow_succ _ n, mul_zero, zero_add] at h0
      simpa [hy] using h0
    obtain ⟨b', hb'⟩ := mem_span_singleton'.1 (hker ▸ h1 : b ∈ span {p})
    refine mem_span_pair.2 ⟨a, b' * y, ?_⟩
    rw [← sub_eq_zero]
    apply hreg
    linear_combination hab - hx' + y ^ (n + 1) * hb'
  refine ⟨fun x hx => ?_⟩
  simp only [smul_eq_mul, mul_top, SModEq.zero] at hx
  refine eq_zero_of_haus p x fun k => ?_
  have : ∃ x', x = p ^ k * x' ∧ ∀ n, x' ∈ span {p ^ n, y ^ n} := by
    induction k with
    | zero => exact ⟨x, by simp, fun n => pair_pow_le p y n (hx _)⟩
    | succ k ih =>
      obtain ⟨z, hz, hz'⟩ := ih
      obtain ⟨w, hw, hw'⟩ := step z hz'
      exact ⟨w, by rw [hz, hw]; ring, hw'⟩
  obtain ⟨z, rfl, -⟩ := this
  exact mul_mem_right _ _ (mem_span_singleton_self _)

end General

section Perf

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

theorem coeff_pow_self (x : Perfection R p) (n : ℕ) :
    Perfection.coeff R p n x ^ p ^ n = Perfection.coeff R p 0 x :=
  Perfection.coeffMonoidHom_pow_p_pow_self x n

theorem perfection_isUnit (x : Perfection R p) (h : IsUnit (Perfection.coeff R p 0 x)) :
    IsUnit x := by
  have hn : ∀ n, IsUnit (Perfection.coeff R p n x) := fun n => by
    rw [← coeff_pow_self x n] at h
    exact (isUnit_pow_iff (pow_ne_zero _ hp.out.ne_zero)).1 h
  let y : Perfection R p := ⟨fun n => ((hn n).unit⁻¹ : Rˣ), fun n => by
    have e : (hn (n + 1)).unit ^ p = (hn n).unit :=
      Units.ext (by simp [Perfection.coeff_pow_p' x n])
    rw [← Units.val_pow_eq_pow_val, inv_pow, e]⟩
  have hy : ∀ n, Perfection.coeff R p n x * Perfection.coeff R p n y = 1 := fun n => by
    rw [Perfection.coeff_mk]
    exact (hn n).mul_val_inv
  refine ⟨⟨x, y, ?_, ?_⟩, rfl⟩
  · ext n; rw [map_mul, hy, map_one]
  · ext n; rw [map_mul, mul_comm, hy, map_one]

theorem coeff_pow_eq_zero {y : Perfection R p} {m : ℕ} (hm : Perfection.coeff R p 0 y ^ m = 0)
    (n N : ℕ) (hN : p ^ n * m ≤ N) : Perfection.coeff R p n y ^ N = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [pow_add, pow_mul, coeff_pow_self, hm, zero_mul]

theorem perfection_haus {y : Perfection R p} (hy : IsNilpotent (Perfection.coeff R p 0 y))
    (x : Perfection R p) (hx : ∀ n, y ^ n ∣ x) : x = 0 := by
  obtain ⟨m, hm⟩ := hy
  ext n
  obtain ⟨c, rfl⟩ := hx (p ^ n * m)
  rw [map_mul, map_pow, coeff_pow_eq_zero hm n _ le_rfl, zero_mul, map_zero]

theorem perfection_tails {y : Perfection R p} (hy : IsNilpotent (Perfection.coeff R p 0 y)) :
    Tails y := by
  obtain ⟨m, hm⟩ := hy
  intro b
  let S : ℕ → ℕ → Perfection R p := fun k N => ∑ i ∈ range N, y ^ i * b (k + i)
  have stab : ∀ k n N, p ^ n * m ≤ N →
      Perfection.coeff R p n (S k N) = Perfection.coeff R p n (S k (p ^ n * m)) := by
    intro k n N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ N hN ih =>
      rw [← ih]
      simp only [S]
      rw [sum_range_succ, map_add, map_mul, map_pow, coeff_pow_eq_zero hm n N hN, zero_mul,
        add_zero]
  have ex : ∀ k, ∃ t : Perfection R p, ∀ n,
      Perfection.coeff R p n t = Perfection.coeff R p n (S k (p ^ n * m)) := fun k =>
    ⟨⟨fun n => Perfection.coeff R p n (S k (p ^ n * m)), fun n => by
      rw [Perfection.coeff_pow_p']
      exact stab k n _
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ n)))⟩, fun _ => rfl⟩
  choose t ht using ex
  refine ⟨t, fun k => ?_⟩
  · ext n
    rw [map_sub, map_mul, ht, ht, ← stab k n _ (Nat.le_succ _), ← map_mul, ← map_sub]
    congr 1
    simp only [S]
    rw [sum_range_succ', mul_sum]
    simp only [pow_zero, one_mul, add_zero]
    rw [eq_sub_iff_add_eq, add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [show k + 1 + i = k + (i + 1) by omega]
    ring

end Perf

section Witt

open WittVector

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

theorem witt_isUnit (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have hmem : c * teichmuller p ((u⁻¹ : Rˣ) : R) - 1 ∈ span {(p : WittVector p R)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      constantCoeff_apply (x := teichmuller p _), teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : WittVector p R)}) hmem
  have h1 := (mem_jacobson_bot.1 hj) 1
  rw [mul_one, sub_add_cancel] at h1
  exact isUnit_of_mul_isUnit_left h1

theorem witt_complete [IsDomain R] (y : WittVector p R) (ht : Tails (constantCoeff y))
    (hh : ∀ x : R, (∀ n, constantCoeff y ^ n ∣ x) → x = 0) :
    IsAdicComplete (span {(p : WittVector p R), y}) (WittVector p R) ∧
      IsAdicComplete (span {y}) (WittVector p R) := by
  have hT : Tails y := by
    refine tails_of_mod (p : WittVector p R) y fun b => ?_
    obtain ⟨t, ht⟩ := ht fun n => constantCoeff (b n)
    choose s hs using fun n => constantCoeff_surjective p (t n)
    have : ∀ n, ∃ c, c * (p : WittVector p R) = b n - (s n - y * s (n + 1)) := by
      intro n
      rw [← mem_span_singleton', ← ker_constantCoeff, RingHom.mem_ker, map_sub, map_sub, map_mul,
        hs, hs, ← ht, sub_self]
    choose c hc using this
    exact ⟨s, c, fun n => by linear_combination -hc n⟩
  have hH : IsHausdorff (span {(p : WittVector p R), y}) (WittVector p R) :=
    hausdorff_pair constantCoeff _ y ker_constantCoeff eq_zero_of_p_mul_eq_zero hh
  have hP := precomplete_pair (summ_of_precomplete (p : WittVector p R)) (summ_of_tails hT)
  have hP' := precomplete_of_summ (summ_of_tails hT)
  have hH' : IsHausdorff (span {y}) (WittVector p R) := by
    refine ⟨fun x hx => hH.haus' x fun n => ?_⟩
    have := hx n
    simp only [smul_eq_mul, mul_top, SModEq.zero] at this ⊢
    exact Ideal.pow_right_mono (span_mono (by simp)) n this
  exact ⟨{ hH, hP with }, { hH', hP' with }⟩

end Witt

theorem nilpotent_of_not_isUnit (l : ℕ) [hl : Fact l.Prime] (x : ModP (OC l) l)
    (hx : ¬ IsUnit x) : IsNilpotent x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := span {((l : ℕ) : OC l)}) x
  have hv := PadicComplexInt.integers l
  have h1 : Valued.v (algebraMap (OC l) (PadicComplex l) a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) fun e => hx ((hv.isUnit_of_one' e).map _)
  have h2 : 0 < Valued.v (algebraMap (OC l) (PadicComplex l) ((l : ℕ) : OC l)) := by
    rw [map_natCast, PadicComplex.valuation_p]
    have := hl.out.pos
    positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one h2 h1
  refine ⟨m, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton, ← hv.le_iff_dvd, map_pow,
    map_pow]
  exact hm.le

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ y : Ainf l, ¬ IsUnit y →
    IsAdicComplete (Ideal.span {((l : ℕ) : Ainf l), y}) (Ainf l) ∧
      IsAdicComplete (Ideal.span {y}) (Ainf l) := by
  intro l _ y hy
  have h1 : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 (WittVector.constantCoeff y)) :=
    nilpotent_of_not_isUnit l _ fun h => hy (witt_isUnit y (perfection_isUnit _ h))
  exact witt_complete y (perfection_tails h1) (perfection_haus h1)

end GlobalTheory.Per.AinfComplete
