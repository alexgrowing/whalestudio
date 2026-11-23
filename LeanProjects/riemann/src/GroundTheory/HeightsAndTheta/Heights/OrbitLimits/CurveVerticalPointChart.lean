import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace CurveVerticalPointChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem prod_pow_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e f : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (e + f) k = (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

theorem form_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem form_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine form_add hf ?_
  intro m hm
  rw [support_neg] at hm
  exact hg m hm

theorem form_C (n : ℤ) : IsMultiHomog (C n : MRing ι) 0 := by
  classical
  intro m hm k
  rw [C_apply] at hm
  have : m = 0 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst this
  simp

theorem mem_of_aeval_eq (y : (Σ k, ι k) → Ω) {W : Ideal (MRing ι)} (hPW : mCoordIdeal y ≤ W)
    {f g : MRing ι} {a a' : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a') (haa : a = a')
    (he : aeval y f = aeval y g) (hfW : f ∈ W) : g ∈ W := by
  subst haa
  have h0 : f - g ∈ mCoordIdeal y :=
    HilbertSamuel.SmallSectionsNonzero.mem_mCoordIdeal_of_aeval_eq_zero y (form_sub hf hg)
      (by rw [map_sub, he, sub_self])
  have h1 := W.sub_mem hfW (hPW h0)
  rwa [sub_sub_cancel] at h1

theorem chartMono_notMem {W : Ideal (MRing ι)} (hWp : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (e : K → ℕ) :
    HilbertSamuel.SmallSectionsNonzero.chartMono c e ∉ W := by
  classical
  rw [HilbertSamuel.SmallSectionsNonzero.chartMono, Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hc k (hWp.mem_of_pow_mem _ hk)

theorem mem_of_chartMono_mul {W : Ideal (MRing ι)} (hWp : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) {e : K → ℕ} {f : MRing ι}
    (h : HilbertSamuel.SmallSectionsNonzero.chartMono c e * f ∈ W) : f ∈ W :=
  (hWp.mem_or_mem h).resolve_left (chartMono_notMem hWp hc e)

theorem exists_rep (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRingZ y c) :
    ∃ (e : K → ℕ) (k : MRing ι), IsMultiHomog k e ∧ r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y k := by
  obtain ⟨e, k, hk, he⟩ :=
    HilbertSamuel.SmallSectionsNonzero.exists_form_of_mem_chartRingZ y c hyc hr
  exact ⟨e, k, hk, he.symm⟩

theorem mem_chart (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : curveRing y) :
    (b : Ω) ∈ chartRingZ y c :=
  mem_curveRing.mp b.2 c hyc

def chartPrime (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (W : Ideal (MRing ι)) : Set Ω :=
  {r | ∃ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e ∧ g ∈ W ∧ r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y g}

theorem mem_chartPrime_iff (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) {r : Ω}
    {e : K → ℕ} {k : MRing ι} (hk : IsMultiHomog k e) (hr : r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y k) :
    r ∈ chartPrime y c W ↔ k ∈ W := by
  constructor
  · rintro ⟨d, g, hg, hgW, hd⟩
    apply mem_of_chartMono_mul hWp hc (e := d)
    refine mem_of_aeval_eq y hPW
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hg)
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d) hk)
      (add_comm e d) ?_ (W.mul_mem_left _ hgW)
    simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ e k)) * hd + (∏ k, y ⟨k, c k⟩ ^ d k) * hr
  · intro hkW
    exact ⟨e, k, hk, hkW, hr⟩

theorem chartPrime_add (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)} {r r' : Ω}
    (hr : r ∈ chartPrime y c W) (hr' : r' ∈ chartPrime y c W) : r + r' ∈ chartPrime y c W := by
  obtain ⟨d, g, hg, hgW, hd⟩ := hr
  obtain ⟨e, g', hg', hg'W, he⟩ := hr'
  have h1 := Inter.AvoidRing.isMultiHomog_mul hg (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e)
  have h2 := Inter.AvoidRing.isMultiHomog_mul hg' (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d)
  rw [add_comm e d] at h2
  refine ⟨d + e, _, form_add h1 h2, W.add_mem (W.mul_mem_right _ hgW) (W.mul_mem_right _ hg'W), ?_⟩
  simp only [map_add, map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
  rw [prod_pow_add]
  linear_combination (∏ k, y ⟨k, c k⟩ ^ e k) * hd + (∏ k, y ⟨k, c k⟩ ^ d k) * he

theorem chartPrime_mul (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {W : Ideal (MRing ι)} {a r : Ω} (ha : a ∈ chartRingZ y c) (hr : r ∈ chartPrime y c W) :
    a * r ∈ chartPrime y c W := by
  obtain ⟨d, g, hg, hgW, hd⟩ := hr
  obtain ⟨e, k, hk, hae⟩ := exists_rep y hyc ha
  refine ⟨e + d, k * g, Inter.AvoidRing.isMultiHomog_mul hk hg, W.mul_mem_left _ hgW, ?_⟩
  rw [map_mul, prod_pow_add]
  linear_combination (r * ∏ k, y ⟨k, c k⟩ ^ d k) * hae + (aeval y k) * hd

def chartPrimeB (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (W : Ideal (MRing ι))
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Ideal (curveRing y) where
  carrier := {b | (b : Ω) ∈ chartPrime y c W}
  add_mem' {a b} ha hb := by
    change ((a : Ω) + b) ∈ chartPrime y c W
    exact chartPrime_add y ha hb
  zero_mem' := ⟨0, 0, fun m hm => by simp at hm, W.zero_mem, by simp⟩
  smul_mem' a b hb := by
    change ((a : Ω) * b) ∈ chartPrime y c W
    exact chartPrime_mul y hyc (mem_chart y hyc a) hb

theorem mem_chartPrimeB {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    {hyc : ∀ k, y ⟨k, c k⟩ ≠ 0} {b : curveRing y} : b ∈ chartPrimeB y c W hyc ↔ (b : Ω) ∈ chartPrime y c W :=
  Iff.rfl

theorem chartPrimeB_isPrime (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : (chartPrimeB y c W hyc).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    have h1 := (mem_chartPrime_iff y hPW hWp hc (r := ((1 : curveRing y) : Ω)) (e := 0) (k := 1)
      Inter.AvoidRing.isMultiHomog_one (by simp)).mp (mem_chartPrimeB.mp h)
    exact hWp.ne_top ((Ideal.eq_top_iff_one W).mpr h1)
  · intro a b hab
    obtain ⟨e, k, hk, ha⟩ := exists_rep y hyc (mem_chart y hyc a)
    obtain ⟨e', k', hk', hb⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hkk : k * k' ∈ W := (mem_chartPrime_iff y hPW hWp hc (r := ((a * b : curveRing y) : Ω))
      (Inter.AvoidRing.isMultiHomog_mul hk hk') (by
        rw [Subring.coe_mul, map_mul, prod_pow_add]
        linear_combination ((b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e' k) * ha + (aeval y k) * hb)).mp
      (mem_chartPrimeB.mp hab)
    rcases hWp.mem_or_mem hkk with h | h
    · exact Or.inl ⟨e, k, hk, h, ha⟩
    · exact Or.inr ⟨e', k', hk', h, hb⟩

theorem curvePtIdeal_eq (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : curvePtIdeal y W = chartPrimeB y c W hyc := by
  apply le_antisymm
  · rw [curvePtIdeal, Ideal.span_le]
    rintro b ⟨δ, g, h, hg, hh, hgW, hhW, hb⟩
    obtain ⟨e, k, hk, hbk⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hkh : k * h ∈ W := mem_of_aeval_eq y hPW
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hg)
      (Inter.AvoidRing.isMultiHomog_mul hk hh) rfl
      (by
        simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
        linear_combination (-(∏ k, y ⟨k, c k⟩ ^ e k)) * hb + (aeval y h) * hbk)
      (W.mul_mem_left _ hgW)
    exact ⟨e, k, hk, (hWp.mem_or_mem hkh).resolve_right hhW, hbk⟩
  · intro b hb
    obtain ⟨d, g, hg, hgW, hd⟩ := mem_chartPrimeB.mp hb
    apply Ideal.subset_span
    refine ⟨d, g, HilbertSamuel.SmallSectionsNonzero.chartMono c d, hg,
      HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d, hgW, chartMono_notMem hWp hc d, ?_⟩
    rw [HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
    exact hd

theorem chartPrimeB_isMaximal (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hB : Module.Finite ℤ (curveRing y))
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {n : ℤ} (hn : n ≠ 0) (hnW : (C n : MRing ι) ∈ W) :
    (chartPrimeB y c W hyc).IsMaximal := by
  have := chartPrimeB_isPrime y hPW hWp hc hyc
  have hnm : (n : curveRing y) ∈ chartPrimeB y c W hyc := by
    refine mem_chartPrimeB.mpr ⟨0, C n, form_C n, hnW, ?_⟩
    simp
  have : Module.Finite ℤ (curveRing y ⧸ chartPrimeB y c W hyc) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ (chartPrimeB y c W hyc)).toLinearMap
      Ideal.Quotient.mk_surjective
  have htor : Module.IsTorsion ℤ (curveRing y ⧸ chartPrimeB y c W hyc) := by
    intro x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    show n • Ideal.Quotient.mk _ b = 0
    rw [zsmul_eq_mul, ← map_intCast (Ideal.Quotient.mk (chartPrimeB y c W hyc)), ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hnm
  have : Finite (curveRing y ⧸ chartPrimeB y c W hyc) := Module.finite_of_fg_torsion _ htor
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

def locSub (y : (Σ k, ι k) → Ω) (m : Ideal (curveRing y)) (hm : m.IsPrime) : Subring Ω where
  carrier := {r | ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * r = a}
  mul_mem' {r r'} := by
    rintro ⟨a, b, hb, h⟩ ⟨a', b', hb', h'⟩
    refine ⟨a * a', b * b', fun h'' => (hm.mem_or_mem h'').elim hb hb', ?_⟩
    rw [Subring.coe_mul, Subring.coe_mul]
    linear_combination ((b' : Ω) * r') * h + (a : Ω) * h'
  one_mem' := ⟨1, 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp⟩
  add_mem' {r r'} := by
    rintro ⟨a, b, hb, h⟩ ⟨a', b', hb', h'⟩
    refine ⟨a * b' + b * a', b * b', fun h'' => (hm.mem_or_mem h'').elim hb hb', ?_⟩
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_mul, Subring.coe_mul]
    linear_combination (b' : Ω) * h + (b : Ω) * h'
  zero_mem' := ⟨0, 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp⟩
  neg_mem' {r} := by
    rintro ⟨a, b, hb, h⟩
    refine ⟨-a, b, hb, ?_⟩
    rw [Subring.coe_neg]
    linear_combination -h

theorem mem_locSub {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} {hm : m.IsPrime} {r : Ω} :
    r ∈ locSub y m hm ↔ ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * r = a :=
  Iff.rfl

theorem chart_le_locSub (y : (Σ k, ι k) → Ω) (m : Ideal (curveRing y)) (hm : m.IsPrime) (c : ∀ k, ι k)
    (h : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y m hm) {r : Ω} (hr : r ∈ chartRingZ y c) :
    r ∈ locSub y m hm := by
  rw [chartRingZ] at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact h p
  | algebraMap n =>
    rw [algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ n
  | add x x' _ _ hx hx' => exact add_mem hx hx'
  | mul x x' _ _ hx hx' => exact mul_mem hx hx'

end CurveVerticalPointChart

end

end GroundTheory.Heights₂.Heights.Targets
