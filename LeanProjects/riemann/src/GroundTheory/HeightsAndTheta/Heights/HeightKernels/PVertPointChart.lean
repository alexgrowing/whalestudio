import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CharacterNondegenerate
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace VerticalPointChart

variable {T : Type} [Fintype T] {K' : Type} [Field K']

theorem form_X (t : T) : IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) := by
  have h := Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := fun _ : Unit => T) () t
  convert h using 1
  funext u
  cases u
  simp

theorem form_mul {f g : MRing (fun _ : Unit => T)} {a b : ℕ} (hf : IsMultiHomog f (fun _ => a))
    (hg : IsMultiHomog g (fun _ => b)) : IsMultiHomog (f * g) (fun _ => a + b) :=
  Inter.AvoidRing.isMultiHomog_mul hf hg

theorem form_X_pow (t : T) (n : ℕ) :
    IsMultiHomog ((X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ n) (fun _ => n) := by
  induction n with
  | zero => rw [pow_zero]; exact Inter.AvoidRing.isMultiHomog_one
  | succ n ih => rw [pow_succ]; exact form_mul ih (form_X t)

theorem form_add {f g : MRing (fun _ : Unit => T)} {a : ℕ} (hf : IsMultiHomog f (fun _ => a))
    (hg : IsMultiHomog g (fun _ => a)) : IsMultiHomog (f + g) (fun _ => a) := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem form_sub {f g : MRing (fun _ : Unit => T)} {a : ℕ} (hf : IsMultiHomog f (fun _ => a))
    (hg : IsMultiHomog g (fun _ => a)) : IsMultiHomog (f - g) (fun _ => a) := by
  rw [sub_eq_add_neg]
  refine form_add hf ?_
  intro m hm
  rw [support_neg] at hm
  exact hg m hm

theorem form_zero (a : ℕ) : IsMultiHomog (0 : MRing (fun _ : Unit => T)) (fun _ => a) := by
  intro m hm
  simp at hm

theorem form_C (n : ℤ) : IsMultiHomog (C n : MRing (fun _ : Unit => T)) (fun _ => 0) := by
  classical
  intro m hm k
  rw [C_apply] at hm
  have : m = 0 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst this
  simp

theorem mem_of_aeval_eq (y : (Σ _ : Unit, T) → K') {W : Ideal (MRing (fun _ : Unit => T))}
    (hPW : mCoordIdeal y ≤ W) {f g : MRing (fun _ : Unit => T)} {n n' : ℕ}
    (hf : IsMultiHomog f (fun _ => n)) (hg : IsMultiHomog g (fun _ => n')) (hnn : n = n')
    (he : aeval y f = aeval y g) (hfW : f ∈ W) : g ∈ W := by
  subst hnn
  have h0 : f - g ∈ mCoordIdeal y :=
    HilbertSamuel.SmallSectionsNonzero.mem_mCoordIdeal_of_aeval_eq_zero y (form_sub hf hg)
      (by rw [map_sub, he, sub_self])
  have h1 := W.sub_mem hfW (hPW h0)
  rwa [sub_sub_cancel] at h1

omit [Fintype T] in

theorem mem_of_X_pow_mul {W : Ideal (MRing (fun _ : Unit => T))} (hWp : W.IsPrime) {t : T}
    (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W) {n : ℕ} {f : MRing (fun _ : Unit => T)}
    (h : X ⟨(), t⟩ ^ n * f ∈ W) : f ∈ W :=
  (hWp.mem_or_mem h).resolve_left fun h' => ht (hWp.mem_of_pow_mem _ h')

theorem exists_rep (y : (Σ _ : Unit, T) → K') {t : T} (hyt : y ⟨(), t⟩ ≠ 0) {r : K'}
    (hr : r ∈ chartRingZ y (fun _ => t)) :
    ∃ (e : ℕ) (k : MRing (fun _ : Unit => T)), IsMultiHomog k (fun _ => e) ∧
      r * y ⟨(), t⟩ ^ e = aeval y k := by
  obtain ⟨δ, k, hk, he⟩ :=
    HilbertSamuel.SmallSectionsNonzero.exists_form_of_mem_chartRingZ y (fun _ => t) (fun _ => hyt) hr
  have hδ : δ = fun _ => δ () := funext fun u => by cases u; rfl
  rw [hδ] at hk
  refine ⟨δ (), k, hk, ?_⟩
  rw [he, Fintype.prod_unique]

omit [Fintype T] in

theorem mem_chart (y : (Σ _ : Unit, T) → K') {t : T} (hyt : y ⟨(), t⟩ ≠ 0) (b : curveRing y) :
    (b : K') ∈ chartRingZ y (fun _ => t) :=
  mem_curveRing.mp b.2 (fun _ => t) (fun _ => hyt)

def chartPrime (y : (Σ _ : Unit, T) → K') (t : T) (W : Ideal (MRing (fun _ : Unit => T))) : Set K' :=
  {r | ∃ (d : ℕ) (g : MRing (fun _ : Unit => T)), IsMultiHomog g (fun _ => d) ∧ g ∈ W ∧
    r * y ⟨(), t⟩ ^ d = aeval y g}

theorem mem_chartPrime_iff (y : (Σ _ : Unit, T) → K') {t : T} {W : Ideal (MRing (fun _ : Unit => T))}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W) {r : K'}
    {e : ℕ} {k : MRing (fun _ : Unit => T)} (hk : IsMultiHomog k (fun _ => e))
    (hr : r * y ⟨(), t⟩ ^ e = aeval y k) : r ∈ chartPrime y t W ↔ k ∈ W := by
  constructor
  · rintro ⟨d, g, hg, hgW, hd⟩
    apply mem_of_X_pow_mul hWp ht (n := d)
    refine mem_of_aeval_eq y hPW (form_mul (form_X_pow t e) hg) (form_mul (form_X_pow t d) hk) (by omega)
      ?_ (W.mul_mem_left _ hgW)
    simp only [map_mul, map_pow, aeval_X]
    linear_combination (-(y ⟨(), t⟩ ^ e)) * hd + (y ⟨(), t⟩ ^ d) * hr
  · intro hkW
    exact ⟨e, k, hk, hkW, hr⟩

theorem chartPrime_add (y : (Σ _ : Unit, T) → K') {t : T} {W : Ideal (MRing (fun _ : Unit => T))} {r r' : K'}
    (hr : r ∈ chartPrime y t W) (hr' : r' ∈ chartPrime y t W) : r + r' ∈ chartPrime y t W := by
  obtain ⟨d, g, hg, hgW, hd⟩ := hr
  obtain ⟨e, g', hg', hg'W, he⟩ := hr'
  have h1 := form_mul (form_X_pow t e) hg
  rw [add_comm e d] at h1
  have h2 : IsMultiHomog (X ⟨(), t⟩ ^ e * g + X ⟨(), t⟩ ^ d * g') (fun _ => d + e) :=
    form_add h1 (form_mul (form_X_pow t d) hg')
  have h3 : X ⟨(), t⟩ ^ e * g + X ⟨(), t⟩ ^ d * g' ∈ W :=
    W.add_mem (W.mul_mem_left _ hgW) (W.mul_mem_left _ hg'W)
  have h4 : (r + r') * y ⟨(), t⟩ ^ (d + e) = aeval y (X ⟨(), t⟩ ^ e * g + X ⟨(), t⟩ ^ d * g') := by
    simp only [map_add, map_mul, map_pow, aeval_X]
    linear_combination (y ⟨(), t⟩ ^ e) * hd + (y ⟨(), t⟩ ^ d) * he
  exact ⟨d + e, _, h2, h3, h4⟩

theorem chartPrime_mul (y : (Σ _ : Unit, T) → K') {t : T} (hyt : y ⟨(), t⟩ ≠ 0)
    {W : Ideal (MRing (fun _ : Unit => T))} {c r : K'} (hc : c ∈ chartRingZ y (fun _ => t))
    (hr : r ∈ chartPrime y t W) : c * r ∈ chartPrime y t W := by
  obtain ⟨d, g, hg, hgW, hd⟩ := hr
  obtain ⟨e, k, hk, hce⟩ := exists_rep y hyt hc
  refine ⟨e + d, k * g, form_mul hk hg, W.mul_mem_left _ hgW, ?_⟩
  rw [map_mul]
  linear_combination (r * y ⟨(), t⟩ ^ d) * hce + (aeval y k) * hd

def chartPrimeB (y : (Σ _ : Unit, T) → K') (t : T) (W : Ideal (MRing (fun _ : Unit => T)))
    (hyt : y ⟨(), t⟩ ≠ 0) : Ideal (curveRing y) where
  carrier := {b | (b : K') ∈ chartPrime y t W}
  add_mem' {a b} ha hb := by
    change ((a : K') + b) ∈ chartPrime y t W
    exact chartPrime_add y ha hb
  zero_mem' := ⟨0, 0, form_zero 0, W.zero_mem, by simp⟩
  smul_mem' c b hb := by
    change ((c : K') * b) ∈ chartPrime y t W
    exact chartPrime_mul y hyt (mem_chart y hyt c) hb

theorem mem_chartPrimeB {y : (Σ _ : Unit, T) → K'} {t : T} {W : Ideal (MRing (fun _ : Unit => T))}
    {hyt : y ⟨(), t⟩ ≠ 0} {b : curveRing y} : b ∈ chartPrimeB y t W hyt ↔ (b : K') ∈ chartPrime y t W :=
  Iff.rfl

theorem chartPrimeB_isPrime (y : (Σ _ : Unit, T) → K') {t : T} {W : Ideal (MRing (fun _ : Unit => T))}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W)
    (hyt : y ⟨(), t⟩ ≠ 0) : (chartPrimeB y t W hyt).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    have h1 := (mem_chartPrime_iff y hPW hWp ht (r := ((1 : curveRing y) : K')) (e := 0) (k := 1)
      Inter.AvoidRing.isMultiHomog_one (by simp)).mp (mem_chartPrimeB.mp h)
    exact hWp.ne_top ((Ideal.eq_top_iff_one W).mpr h1)
  · intro a b hab
    obtain ⟨e, k, hk, ha⟩ := exists_rep y hyt (mem_chart y hyt a)
    obtain ⟨e', k', hk', hb⟩ := exists_rep y hyt (mem_chart y hyt b)
    have hkk : k * k' ∈ W := (mem_chartPrime_iff y hPW hWp ht (r := ((a * b : curveRing y) : K')) (form_mul hk hk')
      (by rw [Subring.coe_mul, map_mul]; linear_combination ((b : K') * y ⟨(), t⟩ ^ e') * ha + (aeval y k) * hb)).mp (mem_chartPrimeB.mp hab)
    rcases hWp.mem_or_mem hkk with h | h
    · exact Or.inl ⟨e, k, hk, h, ha⟩
    · exact Or.inr ⟨e', k', hk', h, hb⟩

theorem curvePtIdeal_eq (y : (Σ _ : Unit, T) → K') {t : T} {W : Ideal (MRing (fun _ : Unit => T))}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W)
    (hyt : y ⟨(), t⟩ ≠ 0) : curvePtIdeal y W = chartPrimeB y t W hyt := by
  apply le_antisymm
  · rw [curvePtIdeal, Ideal.span_le]
    rintro b ⟨δ, g, h, hg, hh, hgW, hhW, hb⟩
    obtain ⟨e, k, hk, hbk⟩ := exists_rep y hyt (mem_chart y hyt b)
    have hδ : δ = fun _ => δ () := funext fun u => by cases u; rfl
    rw [hδ] at hg hh
    have hkh : k * h ∈ W := mem_of_aeval_eq y hPW (form_mul (form_X_pow t e) hg) (form_mul hk hh) rfl
      (by simp only [map_mul, map_pow, aeval_X]; linear_combination (-(y ⟨(), t⟩ ^ e)) * hb + (aeval y h) * hbk) (W.mul_mem_left _ hgW)
    exact ⟨e, k, hk, (hWp.mem_or_mem hkh).resolve_right hhW, hbk⟩
  · intro b hb
    obtain ⟨d, g, hg, hgW, hd⟩ := mem_chartPrimeB.mp hb
    apply Ideal.subset_span
    have hX : IsMultiHomog ((X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ d) (fun _ => d) := form_X_pow t d
    have hXW : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ d ∉ W := fun h => ht (hWp.mem_of_pow_mem _ h)
    have hv : (b : K') * aeval y ((X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ d) = aeval y g := by
      rw [map_pow, aeval_X]
      exact hd
    exact ⟨fun _ => d, g, _, hg, hX, hgW, hXW, hv⟩

theorem chartPrimeB_isMaximal (y : (Σ _ : Unit, T) → K') {t : T} {W : Ideal (MRing (fun _ : Unit => T))}
    (hB : Module.Finite ℤ (curveRing y))
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W)
    (hyt : y ⟨(), t⟩ ≠ 0) {n : ℤ} (hn : n ≠ 0) (hnW : (C n : MRing (fun _ : Unit => T)) ∈ W) :
    (chartPrimeB y t W hyt).IsMaximal := by
  have := chartPrimeB_isPrime y hPW hWp ht hyt
  have hnm : (n : curveRing y) ∈ chartPrimeB y t W hyt := by
    refine mem_chartPrimeB.mpr ⟨0, C n, form_C n, hnW, ?_⟩
    simp
  have : Module.Finite ℤ (curveRing y ⧸ chartPrimeB y t W hyt) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ (chartPrimeB y t W hyt)).toLinearMap
      Ideal.Quotient.mk_surjective
  have htor : Module.IsTorsion ℤ (curveRing y ⧸ chartPrimeB y t W hyt) := by
    intro x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    show n • Ideal.Quotient.mk _ b = 0
    rw [zsmul_eq_mul, ← map_intCast (Ideal.Quotient.mk (chartPrimeB y t W hyt)), ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hnm
  have : Finite (curveRing y ⧸ chartPrimeB y t W hyt) := Module.finite_of_fg_torsion _ htor
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

def locSub (y : (Σ _ : Unit, T) → K') (m : Ideal (curveRing y)) (hm : m.IsPrime) : Subring K' where
  carrier := {r | ∃ a b : curveRing y, b ∉ m ∧ (b : K') * r = a}
  mul_mem' {r r'} := by
    rintro ⟨a, b, hb, h⟩ ⟨a', b', hb', h'⟩
    refine ⟨a * a', b * b', fun h'' => (hm.mem_or_mem h'').elim hb hb', ?_⟩
    rw [Subring.coe_mul, Subring.coe_mul]
    linear_combination ((b' : K') * r') * h + (a : K') * h'
  one_mem' := ⟨1, 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp⟩
  add_mem' {r r'} := by
    rintro ⟨a, b, hb, h⟩ ⟨a', b', hb', h'⟩
    refine ⟨a * b' + b * a', b * b', fun h'' => (hm.mem_or_mem h'').elim hb hb', ?_⟩
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_mul, Subring.coe_mul]
    linear_combination (b' : K') * h + (b : K') * h'
  zero_mem' := ⟨0, 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp⟩
  neg_mem' {r} := by
    rintro ⟨a, b, hb, h⟩
    refine ⟨-a, b, hb, ?_⟩
    rw [Subring.coe_neg]
    linear_combination -h

omit [Fintype T] in

theorem mem_locSub {y : (Σ _ : Unit, T) → K'} {m : Ideal (curveRing y)} {hm : m.IsPrime} {r : K'} :
    r ∈ locSub y m hm ↔ ∃ a b : curveRing y, b ∉ m ∧ (b : K') * r = a :=
  Iff.rfl

omit [Fintype T] in

theorem chart_le_locSub (y : (Σ _ : Unit, T) → K') (m : Ideal (curveRing y)) (hm : m.IsPrime) (t : T)
    (h : ∀ u : T, y ⟨(), u⟩ / y ⟨(), t⟩ ∈ locSub y m hm) {r : K'} (hr : r ∈ chartRingZ y (fun _ => t)) :
    r ∈ locSub y m hm := by
  rw [chartRingZ] at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    exact h u
  | algebraMap n =>
    rw [algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ n
  | add x x' _ _ hx hx' => exact add_mem hx hx'
  | mul x x' _ _ hx hx' => exact mul_mem hx hx'

end VerticalPointChart

open VerticalPointChart in

theorem VertPointChart.proof (hC : CurveCharts.Statement) : VertPointChart.Statement := by
  intro T _ K' _ _ y s hy hs hsP W hW t ht
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyt : y ⟨(), t⟩ ≠ 0 := fun h0 =>
    ht (hPW (HilbertSamuel.SmallSectionsNonzero.X_mem_mCoordIdeal y _ h0))

  have hv := IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full Unit (fun _ => T) (mCoordIdeal y) s (fun _ => 1) hy hs hsP W hW
  rw [IsHorizontal, ← Ne, Submodule.ne_bot_iff] at hv
  obtain ⟨n, hn, hn0⟩ := hv
  have hCB := hC T K' y hy
  have hmax := chartPrimeB_isMaximal y hCB.1 hPW hWp ht hyt hn0 (Ideal.mem_comap.mp hn)
  rw [curvePtIdeal_eq y hPW hWp ht hyt]
  have hmp : (chartPrimeB y t W hyt).IsPrime := hmax.isPrime

  have hrat : ∀ u : T, y ⟨(), u⟩ / y ⟨(), t⟩ ∈ locSub y _ hmp := by
    obtain ⟨t', hyt', h'⟩ := hCB.2.2 _ hmax
    have hinv : y ⟨(), t'⟩ / y ⟨(), t⟩ ∈ locSub y _ hmp := by
      obtain ⟨a, b, hb, hab⟩ := h' t
      have hab' : (a : K') * y ⟨(), t'⟩ = b * y ⟨(), t⟩ := by
        rw [← hab]
        field_simp
      refine mem_locSub.mpr ⟨b, a, ?_, ?_⟩
      · intro ha
        obtain ⟨d, g, hg, hgW, hd⟩ := mem_chartPrimeB.mp ha
        obtain ⟨e, k, hk, hbk⟩ := exists_rep y hyt (mem_chart y hyt b)
        apply hb
        refine mem_chartPrimeB.mpr ⟨e, k, hk, ?_, hbk⟩
        apply mem_of_X_pow_mul hWp ht (n := d + 1)
        refine mem_of_aeval_eq y hPW (form_mul (form_mul hg (form_X t')) (form_X_pow t e))
          (form_mul (form_X_pow t (d + 1)) hk) (by omega) ?_ (W.mul_mem_right _ (W.mul_mem_right _ hgW))
        simp only [map_mul, map_pow, aeval_X]
        linear_combination (-(y ⟨(), t'⟩ * y ⟨(), t⟩ ^ e)) * hd + (y ⟨(), t⟩ ^ (d + 1)) * hbk +
          (y ⟨(), t⟩ ^ d * y ⟨(), t⟩ ^ e) * hab'
      · rw [← hab]
        field_simp
    intro u
    obtain ⟨a, b, hb, hab⟩ := h' u
    have hu : y ⟨(), u⟩ / y ⟨(), t'⟩ ∈ locSub y _ hmp := mem_locSub.mpr ⟨a, b, hb, hab⟩
    have hprod := mul_mem hu hinv
    have he : y ⟨(), u⟩ / y ⟨(), t'⟩ * (y ⟨(), t'⟩ / y ⟨(), t⟩) = y ⟨(), u⟩ / y ⟨(), t⟩ := by
      field_simp
    rwa [he] at hprod
  refine ⟨hmax, fun u => mem_locSub.mp (hrat u), fun d g hg => ⟨fun hgW => ?_, ?_⟩⟩
  · have hr : aeval y g * y ⟨(), t⟩ ^ (-(d : ℤ)) ∈ chartRingZ y (fun _ => t) :=
      HilbertSamuel.NormCountBounded.aeval_mul_zpow_mem y t hg
    obtain ⟨a, b, hb, hab⟩ := mem_locSub.mp (chart_le_locSub y _ hmp t hrat hr)
    rw [zpow_neg, zpow_natCast] at hab
    have hab' : (b : K') * aeval y g = a * y ⟨(), t⟩ ^ d := by
      rw [← hab]
      field_simp
    refine ⟨a, b, ?_, hb, hab'⟩
    obtain ⟨e, k, hk, hbk⟩ := exists_rep y hyt (mem_chart y hyt b)
    refine mem_chartPrimeB.mpr ⟨e + d, k * g, form_mul hk hg, W.mul_mem_left _ hgW, ?_⟩
    rw [map_mul]
    linear_combination (-(y ⟨(), t⟩ ^ e)) * hab' + (aeval y g) * hbk
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨e, w, hw, hwW, hae⟩ := mem_chartPrimeB.mp ha
    obtain ⟨f, k, hk, hbk⟩ := exists_rep y hyt (mem_chart y hyt b)
    have hkW : k ∉ W := fun hkW => hb (mem_chartPrimeB.mpr ⟨f, k, hk, hkW, hbk⟩)
    have h1 : X ⟨(), t⟩ ^ e * (k * g) ∈ W :=
      mem_of_aeval_eq y hPW (form_mul (form_X_pow t (d + f)) hw) (form_mul (form_X_pow t e) (form_mul hk hg))
        (by omega) (by
          simp only [map_mul, map_pow, aeval_X]
          linear_combination (-(y ⟨(), t⟩ ^ (d + f))) * hae + (y ⟨(), t⟩ ^ e * aeval y g) * hbk -
            (y ⟨(), t⟩ ^ e * y ⟨(), t⟩ ^ f) * hab)
        (W.mul_mem_left _ hwW)
    exact (hWp.mem_or_mem (mem_of_X_pow_mul hWp ht h1)).resolve_left hkW

end

end GroundTheory.Heights₂.Heights
