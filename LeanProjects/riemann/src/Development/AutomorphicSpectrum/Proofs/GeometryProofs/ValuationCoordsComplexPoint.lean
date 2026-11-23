import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocVal

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem homog_one : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  exact hf m (by simpa [MvPolynomial.support_neg] using hm) k

open Classical in
theorem homog_X (k : K) (i : ι k) : IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem homog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (homog_one (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hf

theorem homog_coordProd (C : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, C k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, C k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (homog_one (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact homog_mul (homog_pow (homog_X k (C k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem aeval_scale {A : Type} [CommRing A] [Algebra ℤ A] {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a)
    (c : K → A) (z : (Σ k, ι k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ a k) * aeval z g := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ p, c p.1 ^ d p) * ∏ p, z p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  have h2 : ∏ p : (Σ k, ι k), c p.1 ^ d p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  rw [h1, h2]
  ring

theorem mem_mCoordIdeal_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker]
  show aeval (fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1) f = 0
  have e : (fun p : (Σ k, ι k) => (MvPolynomial.C (y p) * MvPolynomial.X p.1 : MvPolynomial K Ω)) =
      fun p => MvPolynomial.X p.1 * MvPolynomial.C (y p) := by
    funext p
    exact mul_comm _ _
  rw [e, aeval_scale hf]
  have e2 : aeval (fun p => (MvPolynomial.C (y p) : MvPolynomial K Ω)) f =
      (MvPolynomial.C : Ω →+* MvPolynomial K Ω).toIntAlgHom (aeval y f) := by
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [e2, h0, map_zero, mul_zero]

variable (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → ℂ)

def IsVal (a : Ω) (v : ℂ) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval w h ≠ 0 ∧
    aeval y g = a * aeval y h ∧ aeval w g = v * aeval w h

variable {y w}

theorem aeval_eq_zero_of (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) (h0 : aeval y f = 0) : aeval w f = 0 :=
  hw.2 f (mem_mCoordIdeal_of_aeval_eq_zero y hf h0)

theorem aeval_ne_zero_of (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) (h0 : aeval w f ≠ 0) : aeval y f ≠ 0 :=
  fun h => h0 (aeval_eq_zero_of hw hf h)

theorem IsVal.unique (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) {a : Ω} {v v' : ℂ}
    (h1 : IsVal y w a v) (h2 : IsVal y w a v') : v = v' := by
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := h1
  obtain ⟨d', g', h', hg', hh', hn', hy', hv'⟩ := h2
  have hF : IsMultiHomog (g * h' + -(g' * h)) (d + d') :=
    homog_add (homog_mul hg hh') (by
      have := homog_neg (homog_mul hg' hh)
      rwa [add_comm d' d] at this)
  have h0 := aeval_eq_zero_of hw hF (by
    simp only [map_add, map_neg, map_mul, hy, hy']
    ring)
  simp only [map_add, map_neg, map_mul, hv, hv'] at h0
  have : (v - v') * (aeval w h * aeval w h') = 0 := by linear_combination h0
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (mul_ne_zero hn hn')

theorem IsVal.add {a b : Ω} {v u : ℂ} (h1 : IsVal y w a v) (h2 : IsVal y w b u) :
    IsVal y w (a + b) (v + u) := by
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := h1
  obtain ⟨d', g', h', hg', hh', hn', hy', hv'⟩ := h2
  refine ⟨d + d', g * h' + g' * h, h * h', homog_add (homog_mul hg hh') ?_, homog_mul hh hh',
    ?_, ?_, ?_⟩
  · have := homog_mul hg' hh
    rwa [add_comm d' d] at this
  · rw [map_mul]; exact mul_ne_zero hn hn'
  · simp only [map_add, map_mul, hy, hy']; ring
  · simp only [map_add, map_mul, hv, hv']; ring

theorem IsVal.mul {a b : Ω} {v u : ℂ} (h1 : IsVal y w a v) (h2 : IsVal y w b u) :
    IsVal y w (a * b) (v * u) := by
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := h1
  obtain ⟨d', g', h', hg', hh', hn', hy', hv'⟩ := h2
  refine ⟨d + d', g * g', h * h', homog_mul hg hg', homog_mul hh hh', ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hn hn'
  · simp only [map_mul, hy, hy']; ring
  · simp only [map_mul, hv, hv']; ring

theorem IsVal.neg {a : Ω} {v : ℂ} (h1 : IsVal y w a v) : IsVal y w (-a) (-v) := by
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := h1
  refine ⟨d, -g, h, homog_neg hg, hh, hn, ?_, ?_⟩
  · simp only [map_neg, hy]; ring
  · simp only [map_neg, hv]; ring

theorem isVal_one : IsVal y w 1 1 :=
  ⟨0, 1, 1, homog_one, homog_one, by simp, by simp, by simp⟩

theorem isVal_zero : IsVal y w 0 0 :=
  ⟨0, 0, 1, homog_zero 0, homog_one, by simp, by simp, by simp⟩

def locRing (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → ℂ) : Subring Ω where
  carrier := {a | ∃ v, IsVal y w a v}
  mul_mem' := fun ⟨v, hv⟩ ⟨u, hu⟩ => ⟨_, hv.mul hu⟩
  one_mem' := ⟨1, isVal_one⟩
  add_mem' := fun ⟨v, hv⟩ ⟨u, hu⟩ => ⟨_, hv.add hu⟩
  zero_mem' := ⟨0, isVal_zero⟩
  neg_mem' := fun ⟨v, hv⟩ => ⟨_, hv.neg⟩

theorem mem_locRing_of {a : Ω} {v : ℂ} (h : IsVal y w a v) : a ∈ locRing y w := ⟨v, h⟩

def locVal (a : locRing y w) : ℂ := Classical.choose a.2

theorem isVal_locVal (a : locRing y w) : IsVal y w a (locVal a) := Classical.choose_spec a.2

theorem locVal_eq (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) {a : locRing y w} {v : ℂ}
    (h : IsVal y w a v) : locVal a = v :=
  (isVal_locVal a).unique hw h

def locHom (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) : locRing y w →+* ℂ where
  toFun := locVal
  map_one' := locVal_eq hw isVal_one
  map_mul' a b := locVal_eq hw ((isVal_locVal a).mul (isVal_locVal b))
  map_zero' := locVal_eq hw isVal_zero
  map_add' a b := locVal_eq hw ((isVal_locVal a).add (isVal_locVal b))

theorem isUnit_of_locHom_ne_zero (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) (a : locRing y w)
    (ha : locHom hw a ≠ 0) : IsUnit a := by
  have ha' : locVal a ≠ 0 := ha
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := isVal_locVal a
  have hgw : aeval w g ≠ 0 := by rw [hv]; exact mul_ne_zero ha' hn
  have hgy : aeval y g ≠ 0 := aeval_ne_zero_of hw hg hgw
  have ha0 : (a : Ω) ≠ 0 := fun h0 => hgy (by rw [hy, h0, zero_mul])
  have hinv : IsVal y w (a : Ω)⁻¹ (locVal a)⁻¹ :=
    ⟨d, h, g, hh, hg, hgw, by rw [hy]; field_simp, by rw [hv]; field_simp⟩
  refine IsUnit.of_mul_eq_one ⟨(a : Ω)⁻¹, mem_locRing_of hinv⟩ ?_
  exact Subtype.ext (mul_inv_cancel₀ ha0)

theorem isVal_ratio (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) (k : K) (c e : ι k)
    (hc : w ⟨k, c⟩ ≠ 0) : IsVal y w (y ⟨k, e⟩ / y ⟨k, c⟩) (w ⟨k, e⟩ / w ⟨k, c⟩) := by
  classical
  have hXw : aeval w (X ⟨k, c⟩ : MRing ι) ≠ 0 := by simpa using hc
  have hXy := aeval_ne_zero_of hw (homog_X k c) hXw
  have hyc : y ⟨k, c⟩ ≠ 0 := by simpa using hXy
  refine ⟨Pi.single k 1, X ⟨k, e⟩, X ⟨k, c⟩, homog_X k e, homog_X k c, hXw, ?_, ?_⟩
  · simp only [aeval_X]; field_simp
  · simp only [aeval_X]; field_simp

theorem isVal_section (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) {a : K → ℤ} {s : Ω} {v : ℂ}
    {C : ∀ k, ι k} (hv : Small.HasVal y a s w v) (hC : ∀ k, w ⟨k, C k⟩ ≠ 0) :
    IsVal y w (s * ∏ k, y ⟨k, C k⟩ ^ (-a k)) (v * ∏ k, w ⟨k, C k⟩ ^ (-a k)) := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hn, hval⟩ := hv
  have hyC : ∀ k, y ⟨k, C k⟩ ≠ 0 := fun k => by
    have := aeval_ne_zero_of hw (homog_X k (C k)) (by simpa using hC k)
    simpa using this
  have eW : ∀ e : K → ℕ, aeval w (∏ k, (X ⟨k, C k⟩ : MRing ι) ^ e k) = ∏ k, w ⟨k, C k⟩ ^ e k := by
    intro e; simp [map_prod]
  have eY : ∀ e : K → ℕ, aeval y (∏ k, (X ⟨k, C k⟩ : MRing ι) ^ e k) = ∏ k, y ⟨k, C k⟩ ^ e k := by
    intro e; simp [map_prod]
  have shift : ∀ {F : Type} [Field F] (t : ∀ k, F), (∀ k, t k ≠ 0) →
      (∏ k, t k ^ (-a k)) * ∏ k, t k ^ dg k = ∏ k, t k ^ dh k := by
    intro F _ t ht
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast (t k) (dg k), ← zpow_natCast (t k) (dh k), ← zpow_add₀ (ht k), hd k]
    congr 1
    ring
  have hG : IsMultiHomog (g * ∏ k, (X ⟨k, C k⟩ : MRing ι) ^ dh k) (dg + dh) :=
    homog_mul hg (homog_coordProd C dh)
  have hH : IsMultiHomog (h * ∏ k, (X ⟨k, C k⟩ : MRing ι) ^ dg k) (dg + dh) := by
    have := homog_mul hh (homog_coordProd C dg)
    rwa [add_comm] at this
  refine ⟨dg + dh, _, _, hG, hH, ?_, ?_, ?_⟩
  · rw [map_mul, eW]
    exact mul_ne_zero hn (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hC k))
  · rw [map_mul, map_mul, eY, eY, hy, ← shift (fun k => y ⟨k, C k⟩) hyC]
    ring
  · rw [map_mul, map_mul, eW, eW, hval, ← shift (fun k => w ⟨k, C k⟩) hC]
    ring

theorem exists_locRing_val (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type)
    [Field Ω] (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → ℂ)
    (hw : w ∈ Small.ptsOver ℂ (mCoordIdeal y)) :
    ∃ (W : Subring Ω) (φ : W →+* ℂ), (∀ a : W, φ a ≠ 0 → IsUnit a) ∧
      (∀ (k : K) (c e : ι k), w ⟨k, c⟩ ≠ 0 →
        ∃ h : y ⟨k, e⟩ / y ⟨k, c⟩ ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) ∧
      ∀ (a : K → ℤ) (s : Ω) (v : ℂ) (C : ∀ k, ι k), Small.HasVal y a s w v →
        (∀ k, w ⟨k, C k⟩ ≠ 0) →
        ∃ h : s * ∏ k, y ⟨k, C k⟩ ^ (-a k) ∈ W, φ ⟨_, h⟩ * ∏ k, w ⟨k, C k⟩ ^ a k = v := by
  refine ⟨locRing y w, locHom hw, isUnit_of_locHom_ne_zero hw, ?_, ?_⟩
  · intro k c e hc
    have hv := isVal_ratio hw k c e hc
    refine ⟨mem_locRing_of hv, ?_⟩
    have : locVal (⟨_, mem_locRing_of hv⟩ : locRing y w) = _ := locVal_eq hw hv
    show locVal _ * _ = _
    rw [this]
    field_simp
  · intro a s v C hv hC
    have hv' := isVal_section hw hv hC
    refine ⟨mem_locRing_of hv', ?_⟩
    have : locVal (⟨_, mem_locRing_of hv'⟩ : locRing y w) = _ := locVal_eq hw hv'
    show locVal _ * _ = _
    rw [this, mul_assoc, ← Finset.prod_mul_distrib]
    have : ∀ k, w ⟨k, C k⟩ ^ (-a k) * w ⟨k, C k⟩ ^ a k = 1 := fun k => by
      rw [← zpow_add₀ (hC k)]
      simp
    rw [Finset.prod_congr rfl fun k _ => this k]
    simp

end GlobalTheory.CompanionTheory.Ar.LocVal
