import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PowerBlockMetric

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem homog_congr {f : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (h : ∀ k, a k = b k) :
    IsMultiHomog f b :=
  fun m hm k => (hf m hm k).trans (h k)

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := fun m hm => by simp at hm

theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact hf m hm
  · exact hg m hm

theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a :=
  fun m hm => hf m (by rwa [support_neg] at hm)

theorem homog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact homog_add hf (homog_neg hg)

theorem homog_sum {J : Type} (s : Finset J) {f : J → MRing ι} {a : K → ℕ}
    (h : ∀ j ∈ s, IsMultiHomog (f j) a) : IsMultiHomog (∑ j ∈ s, f j) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_zero (ι := ι) a
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact homog_add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem homog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem homog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem homog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  obtain ⟨k, i⟩ := p
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    rw [Pi.single_eq_same, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hb (eq_of_heq (Sigma.mk.inj_iff.mp e).2).symm
    · simp
  · rw [Pi.single_eq_of_ne h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (congrArg Sigma.fst e).symm

theorem homog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (homog_one (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hf

def chartMon (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k

theorem homog_chartMon (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMon c d) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (homog_one (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact homog_mul (homog_pow (homog_X ⟨k, c k⟩) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rw [e] at this
  exact this

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMon, map_prod]

theorem eval_chartMon (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMon c d)) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [chartMon, map_prod]

theorem mConeMap_homog (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) =
      ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

theorem vanish {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g : MRing ι}
    {d : K → ℕ} (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : eval z (map (Int.castRingHom ℂ) g) = 0 := by
  refine hz.2 g ?_
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_homog y hg, h0]
  simp

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧ aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  classical
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, homog_X p, ?_⟩
    have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 1 : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
      rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    rw [aeval_X, h1, div_mul_cancel₀ _ (hc p.1)]
  | algebraMap r =>
    exact ⟨0, C r, homog_C r, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * chartMon c δ₂ + e₂ * chartMon c δ₁,
      homog_add (homog_mul h₁ (homog_chartMon c δ₂)) ?_, ?_⟩
    · rw [add_comm δ₁]
      exact homog_mul h₂ (homog_chartMon c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_chartMon, aeval_chartMon, hpow]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * e₂, homog_mul h₁ h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

theorem exists_chartForm (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : K → ℤ) {t : Ω}
    (ht : t * ∏ k, y ⟨k, c k⟩ ^ (-e k) ∈ chartRingZ y c) :
    ∃ (N δ : K → ℕ) (G : MRing ι), IsMultiHomog G δ ∧ (∀ k, (δ k : ℤ) = e k + N k) ∧
      aeval y G = t * ∏ k, y ⟨k, c k⟩ ^ N k := by
  obtain ⟨δ', G', hG', hv'⟩ := exists_form_of_mem_chartRingZ y c hc ht
  refine ⟨fun k => δ' k + (e k).natAbs, fun k => δ' k + (e k + (e k).natAbs).toNat,
    G' * chartMon c (fun k => (e k + (e k).natAbs).toNat), ?_, fun k => ?_, ?_⟩
  · exact homog_congr (homog_mul hG' (homog_chartMon c _)) fun k => rfl
  · dsimp only
    omega
  · rw [map_mul, hv', aeval_chartMon, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    omega

theorem zpow_combine {F : Type*} [Field F] {x : F} (hx : x ≠ 0) {du dw N D : ℕ} {a : ℤ}
    (hw : (dw : ℤ) = a + N) (hle : du + dw ≤ D) :
    x ^ du * x ^ N * x ^ (D - (du + dw)) = x ^ (-a) * x ^ D := by
  simp only [← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  rw [Nat.cast_sub hle]
  push_cast
  omega

theorem y_ne_zero {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {p : Σ k, ι k} (hp : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hX : (X p : MRing ι) ∈ mCoordIdeal y := by
    show X p ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  simpa using hz.2 _ hX

def IsRep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + n * a k) ∧
    aeval y g = s * aeval y h

theorem cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} {g h g' h' : MRing ι}
    (hr : IsRep y a n s g h) (hr' : IsRep y a n s g' h') {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy'⟩ := hr'
  have hF : IsMultiHomog (g * h' - g' * h) (dg + dh') :=
    homog_sub (homog_mul hg hh') (homog_congr (homog_mul hg' hh) fun k => by
      simp only [Pi.add_apply]
      zify
      linear_combination hd' k - hd k)
  have hFy : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have := vanish hz hF hFy
  simp only [map_sub, map_mul, sub_eq_zero] at this
  exact this

theorem exists_rep_at {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ gh : MRing ι × MRing ι, IsRep y a n s gh.1 gh.2 ∧ eval z (map (Int.castRingHom ℂ) gh.2) ≠ 0 := by
  choose c hc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_zero hz (hc k)
  obtain ⟨N, δ, G, hG, hdeg, hGv⟩ := exists_chartForm y c hyc (fun k => (n : ℤ) * a k) (hs c hyc)
  refine ⟨(G, chartMon c N), ⟨δ, N, hG, homog_chartMon c N, fun k => ?_, ?_⟩, ?_⟩
  · linear_combination hdeg k
  · rw [aeval_chartMon]
    exact hGv
  · rw [eval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

theorem metric_ne {A : HermLine ι} {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (n : ℕ) :
    (A.h z : ℂ) ^ n ≠ 0 :=
  pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (A.pos z hz.1).ne')

def val (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℂ := by
  classical
  exact if hsz : s ∈ chartLat y A.a n ∧ z ∈ mcPts (mCoordIdeal y) then
    eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.1) /
      (eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.2) * (A.h z : ℂ) ^ n)
  else 0

theorem val_spec {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h) :
    eval z (map (Int.castRingHom ℂ) g) =
      val y A n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n := by
  have H := (exists_rep_at hs hz).choose_spec
  rw [val, dif_pos ⟨hs, hz⟩]
  have hc := cross hr H.1 hz
  have h1 := H.2
  have h2 := metric_ne (A := A) hz n
  rw [eq_comm, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero h1 h2)]
  linear_combination (-(A.h z : ℂ) ^ n) * hc

theorem secNormAt_eq {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : secNormAt y A n s z = ‖val y A n s z‖ := by
  have hT : 0 < A.h z := A.pos z hz.1
  have hnT : ‖(A.h z : ℂ) ^ n‖ = A.h z ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hT.le]
  have hb : IsBoundedAt y A n ‖val y A n s z‖ s z := by
    intro dg dh g h hg hh hd hy
    rw [val_spec hs hz ⟨dg, dh, hg, hh, hd, hy⟩, norm_mul, norm_mul, hnT]
  refine le_antisymm (secNormAt_le (norm_nonneg _) hb) ?_
  rw [secNormAt]
  refine le_csInf ⟨_, norm_nonneg _, hb⟩ ?_
  rintro c ⟨-, hc⟩
  obtain ⟨⟨g, h⟩, ⟨dg, dh, hg, hh, hd, hy⟩, hne⟩ := exists_rep_at hs hz
  have := hc dg dh g h hg hh hd hy
  rw [val_spec hs hz ⟨dg, dh, hg, hh, hd, hy⟩, norm_mul, norm_mul, hnT, mul_assoc, mul_assoc] at this
  exact le_of_mul_le_mul_right this (mul_pos (norm_pos_iff.mpr hne) (pow_pos hT n))

theorem exists_val_ne {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m N : ℕ} {v : Fin N → Ω}
    (hv : ∀ j, v j ∈ chartLat y A.a m) (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) : ∃ j, val y A m (v j) x ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  choose c hc using hx.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_zero hx (hc k)
  obtain ⟨u, hu, hsum⟩ := hgen c hyc
  have hsum' : ∑ j, u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) = 1 := hsum
  choose δu U hU hUv using fun j => exists_form_of_mem_chartRingZ y c hyc (hu j)
  choose Nj δw g hg hdeg hgv using fun j => exists_chartForm y c hyc (fun k => (m : ℤ) * A.a k) (hv j c hyc)
  set D : K → ℕ := fun k => ∑ j, (δu j k + δw j k) with hD
  have hle : ∀ j k, δu j k + δw j k ≤ D k := fun j k =>
    Finset.single_le_sum (f := fun j => δu j k + δw j k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set Φ : MRing ι := chartMon c D - ∑ j, U j * g j * chartMon c (fun k => D k - (δu j k + δw j k)) with hΦ
  have hΦh : IsMultiHomog Φ D := homog_sub (homog_chartMon c D) (homog_sum _ fun j _ =>
    homog_congr (homog_mul (homog_mul (hU j) (hg j)) (homog_chartMon c _)) fun k => by
      have := hle j k
      simp only [Pi.add_apply]
      omega)
  have hterm : ∀ j, aeval y (U j * g j * chartMon c (fun k => D k - (δu j k + δw j k))) =
      u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ D k := by
    intro j
    rw [map_mul, map_mul, hUv j, hgv j, aeval_chartMon]
    calc u j * (∏ k, y ⟨k, c k⟩ ^ δu j k) * (v j * ∏ k, y ⟨k, c k⟩ ^ Nj j k) *
          ∏ k, y ⟨k, c k⟩ ^ (D k - (δu j k + δw j k))
        = u j * v j * ∏ k, (y ⟨k, c k⟩ ^ δu j k * y ⟨k, c k⟩ ^ Nj j k *
            y ⟨k, c k⟩ ^ (D k - (δu j k + δw j k))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          ring
      _ = u j * v j * ∏ k, (y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k)) * y ⟨k, c k⟩ ^ D k) := by
          congr 1
          exact Finset.prod_congr rfl fun k _ => zpow_combine (hyc k) (hdeg j k) (hle j k)
      _ = _ := by
          rw [Finset.prod_mul_distrib]
          ring
  have hΦy : aeval y Φ = 0 := by
    rw [hΦ, map_sub, map_sum, aeval_chartMon, Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_mul, hsum',
      one_mul, sub_self]
  have hΦz := vanish hx hΦh hΦy
  have hgz : ∀ j, eval x (map (Int.castRingHom ℂ) (g j)) = 0 := fun j => by
    have hrep : IsRep y A.a m (v j) (g j) (chartMon c (Nj j)) :=
      ⟨δw j, Nj j, hg j, homog_chartMon c (Nj j), fun k => by
        have h := hdeg j k
        linarith, by rw [hgv j, aeval_chartMon]⟩
    rw [val_spec (hv j) hx hrep, hall j]
    ring
  simp only [hΦ, map_sub, map_sum, map_mul, hgz, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero,
    eval_chartMon] at hΦz
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)) hΦz

def oldIdx (N : ℕ) (p : Σ k, ι k) : Σ k, addIdx ι N k := ⟨some p.1, p.2⟩

theorem oldIdx_injective (N : ℕ) : Function.Injective (oldIdx (ι := ι) N) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
  subst h1
  have h2 := (Sigma.mk.inj_iff.mp h).2
  have h3 : i = i' := eq_of_heq h2
  rw [h3]

theorem mConeMap_rename (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) (f : MRing ι) :
    mConeMap (addBlock y v) (rename (oldIdx N) f) = rename (R := Ω) some (mConeMap y f) := by
  have key : (mConeMap (addBlock y v)).comp (rename (oldIdx N)) =
      ((rename (R := Ω) (some : K → Option K)).restrictScalars ℤ).comp (mConeMap y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, oldIdx, addBlock]
  exact DFunLike.congr_fun key f

theorem mConeMap_new (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) (j : Fin N) :
    mConeMap (addBlock y v) (X ⟨none, j⟩ : MRing (addIdx ι N)) = MvPolynomial.C (v j) * MvPolynomial.X none := by
  simp [mConeMap, addBlock]

theorem rename_mem {y : (Σ k, ι k) → Ω} {N : ℕ} (v : Fin N → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    rename (oldIdx N) f ∈ mCoordIdeal (addBlock y v) := by
  have hf' : f ∈ RingHom.ker (mConeMap y) := hf
  show _ ∈ RingHom.ker (mConeMap (addBlock y v))
  rw [RingHom.mem_ker, mConeMap_rename, RingHom.mem_ker.mp hf', map_zero]

theorem eval_rename_old {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename (oldIdx N) f)) = eval (basePart₂ z) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]
  rfl

theorem oldPart_mem {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {z : (Σ k, addIdx ι N k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (some k), fun f hf => ?_⟩
  rw [← eval_rename_old]
  exact hz.2 _ (rename_mem v hf)

theorem new_cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n N : ℕ} {v : Fin N → Ω} {j j' : Fin N}
    {g h g' h' : MRing ι} (hr : IsRep y a n (v j) g h) (hr' : IsRep y a n (v j') g' h')
    {z : (Σ k, addIdx ι N k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) :
    z ⟨none, j⟩ * (eval (basePart₂ z) (map (Int.castRingHom ℂ) g') *
        eval (basePart₂ z) (map (Int.castRingHom ℂ) h)) =
      z ⟨none, j'⟩ * (eval (basePart₂ z) (map (Int.castRingHom ℂ) g) *
        eval (basePart₂ z) (map (Int.castRingHom ℂ) h')) := by
  obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy'⟩ := hr'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    simp only [Pi.add_apply]
    zify
    linear_combination hd' k - hd k
  have e1 := mConeMap_homog y (homog_mul hg' hh)
  have e2 := mConeMap_homog y (homog_mul hg hh')
  rw [hdeg] at e1
  have a1 : aeval y (g' * h) = v j' * aeval y h' * aeval y h := by rw [map_mul, hy']
  have a2 : aeval y (g * h') = v j * aeval y h * aeval y h' := by rw [map_mul, hy]
  have hmem : (X ⟨none, j⟩ * rename (oldIdx N) (g' * h) - X ⟨none, j'⟩ * rename (oldIdx N) (g * h') :
      MRing (addIdx ι N)) ∈ mCoordIdeal (addBlock y v) := by
    show _ ∈ RingHom.ker (mConeMap (addBlock y v))
    rw [RingHom.mem_ker, map_sub, map_mul (mConeMap (addBlock y v)), map_mul (mConeMap (addBlock y v)),
      mConeMap_rename, mConeMap_rename, e1, e2, a1, a2, mConeMap_new, mConeMap_new]
    simp only [map_mul, rename_C]
    ring
  have := hz.2 _ hmem
  simp only [map_sub, map_mul, map_X, eval_X, eval_rename_old, sub_eq_zero] at this
  simpa only [map_mul, eval_mul] using this

theorem graph_prop {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m N : ℕ} {v : Fin N → Ω}
    (hv : ∀ j, v j ∈ chartLat y A.a m) (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v)
    {z : (Σ k, addIdx ι N k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) :
    ∃ c : ℂ, ∀ j, z ⟨none, j⟩ = c * val y A m (v j) (basePart₂ z) := by
  have hx := oldPart_mem hz
  obtain ⟨j₀, hj₀⟩ := exists_val_ne hv hgen hx
  choose gh hgh hne using fun j => exists_rep_at (hv j) hx
  refine ⟨z ⟨none, j₀⟩ / val y A m (v j₀) (basePart₂ z), fun j => ?_⟩
  have e := new_cross (hgh j) (hgh j₀) hz
  rw [val_spec (hv j) hx (hgh j), val_spec (hv j₀) hx (hgh j₀)] at e
  have hH := metric_ne (A := A) hx m
  rw [div_mul_eq_mul_div, eq_div_iff hj₀]
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (hne j) (hne j₀)) hH)
  linear_combination e

theorem tangent_old {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {P0 : Ideal (MRing ι)}
    (hP0 : P0 ≤ mCoordIdeal y) {z w : (Σ k, addIdx ι N k) → ℂ}
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w) :
    IsConeTangent (Int.castRingHom ℂ) P0 (basePart₂ z) (basePart₂ w) := by
  classical
  intro f hf
  refine Eq.trans ?_ (hw _ (rename_mem v (hP0 hf)))
  refine Fintype.sum_of_injective (oldIdx N) (oldIdx_injective N) _ _ (fun p hp => ?_) (fun p => ?_)
  · have h0 : pderiv p (map (Int.castRingHom ℂ) (rename (oldIdx N) f)) = 0 := by
      rw [map_rename]
      apply pderiv_eq_zero_of_notMem_vars
      intro hmem
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hmem)
      exact hp ⟨q, rfl⟩
    rw [h0, map_zero, zero_mul]
  · rw [map_rename, pderiv_rename (oldIdx_injective N), eval_rename]
    rfl

theorem leviForm_congr {E : Type} [Fintype E] {φ ψ : (E → ℂ) → ℝ} {z : E → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : E → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact hy.fderiv_eq
  unfold leviForm
  rw [h1.fderiv_eq]

theorem isOpen_blocks {K : Type} [Fintype K] {ι : K → Type} :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def addedBlockNormSq {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) : ℝ := ∑ j : Fin N, ‖z ⟨none, j⟩‖ ^ 2

theorem newSq_pos {N : ℕ} {z : (Σ k, addIdx ι N k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < addedBlockNormSq z := by
  obtain ⟨j, hj⟩ := hz none
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hj) 2)
    (Finset.single_le_sum (f := fun j : Fin N => ‖z ⟨none, j⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j))

theorem contDiff_newSq {N : ℕ} {n : WithTop ℕ∞} : ContDiff ℝ n (addedBlockNormSq (ι := ι) (N := N)) := by
  unfold addedBlockNormSq
  exact ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨none, j⟩ : Σ k, addIdx ι N k))

theorem contDiff_oldPart {N : ℕ} {n : WithTop ℕ∞} : ContDiff ℝ n (basePart₂ (ι := ι) (N := N)) :=
  contDiff_pi.mpr fun p => contDiff_apply ℝ ℂ (⟨some p.1, p.2⟩ : Σ k, addIdx ι N k)

variable [DecidableEq K]

def graphLine (S : ((Σ k, ι k) → ℂ) → ℝ)
    (hSp : ∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x)
    (hSt : ∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) (N : ℕ) :
    HermLine (addIdx ι N) where
  a := unitDeg (none : Option K)
  h z := Real.sqrt (addedBlockNormSq z) / Real.sqrt (S (basePart₂ z))
  pos z hz := div_pos (Real.sqrt_pos.mpr (newSq_pos hz)) (Real.sqrt_pos.mpr (hSp _ fun k => hz (some k)))
  smul c z hc := by
    have h1 : addedBlockNormSq (fun p => c p.1 * z p) = ‖c none‖ ^ 2 * addedBlockNormSq z := by
      simp only [addedBlockNormSq, norm_mul, mul_pow, Finset.mul_sum]
    have h2 : S (basePart₂ (fun p => c p.1 * z p)) = S (basePart₂ z) :=
      hSt (fun k => c (some k)) (basePart₂ z) fun k => hc (some k)
    have h3 : (∏ k, ‖c k‖ ^ (unitDeg (none : Option K)) k) = ‖c none‖ := by
      rw [Fintype.prod_option]
      simp [unitDeg]
    rw [h1, h2, h3, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_div_assoc]

theorem isSmoothHerm_graphLine {S : ((Σ k, ι k) → ℂ) → ℝ}
    (hSp : ∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x)
    (hSt : ∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) {N : ℕ}
    (hSs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S {x | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0}) :
    IsSmoothHerm (graphLine S hSp hSt N) := by
  intro z hz
  have hx : basePart₂ z ∈ {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} := fun k => hz (some k)
  have hS : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => S (basePart₂ z)) z :=
    (hSs.contDiffAt (isOpen_blocks.mem_nhds hx)).comp z contDiff_oldPart.contDiffAt
  show ContDiffWithinAt ℝ _ (fun z => Real.sqrt (addedBlockNormSq z) / Real.sqrt (S (basePart₂ z))) _ z
  exact ((contDiff_newSq.contDiffAt.sqrt (newSq_pos hz).ne').div (hS.sqrt (hSp _ hx).ne')
    (Real.sqrt_pos.mpr (hSp _ hx)).ne').contDiffWithinAt

theorem conj_graphLine {S : ((Σ k, ι k) → ℂ) → ℝ}
    (hSp : ∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x)
    (hSt : ∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) {N : ℕ}
    (hSc : ∀ x : (Σ k, ι k) → ℂ, S (fun p => (starRingEnd ℂ) (x p)) = S x) :
    IsConjInvariantH (graphLine S hSp hSt N) := by
  intro z
  show Real.sqrt (addedBlockNormSq _) / Real.sqrt (S (basePart₂ _)) = Real.sqrt (addedBlockNormSq z) / Real.sqrt (S (basePart₂ z))
  have h1 : addedBlockNormSq (fun p => (starRingEnd ℂ) (z p)) = addedBlockNormSq z := by simp [addedBlockNormSq]
  have h2 : S (basePart₂ (fun p => (starRingEnd ℂ) (z p))) = S (basePart₂ z) := hSc (basePart₂ z)
  rw [h1, h2]

end PowerBlockMetric

open PowerBlockMetric in

theorem PowerBlockMetric.proof (hExt : SectionNormSqExtension.Statement) : PowerBlockMetric.Statement := by
  intro K _ _ ι _ Ω _ y A P0 m N v hP0 hsemi hconj hv hgen
  obtain ⟨S, hSs, hSp, hSt, hSc, hSv, hSl⟩ := hExt K ι Ω y A m N v hsemi.1 hconj hv hgen
  refine ⟨graphLine S hSp hSt N, mCoordIdeal (addBlock y v), rfl, conj_graphLine hSp hSt hSc, le_rfl,
    ⟨isSmoothHerm_graphLine hSp hSt hSs, fun z hz w hw => ?_⟩, fun z hz j => ?_⟩
  · have hU : ∀ᶠ z' in 𝓝 z, z' ∈ {z' : (Σ k, addIdx ι N k) → ℂ | ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0} :=
      isOpen_blocks.mem_nhds hz.1
    have heq : (fun z' => Real.log ((graphLine S hSp hSt N).h z')) =ᶠ[𝓝 z]
        (fun z' : (Σ k, addIdx ι N k) → ℂ =>
          Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) := by
      filter_upwards [hU] with z' hz'
      have h1 := newSq_pos hz'
      have h2 := hSp (basePart₂ z') (fun k => hz' (some k))
      show Real.log (Real.sqrt (addedBlockNormSq z') / Real.sqrt (S (basePart₂ z'))) = _
      rw [Real.log_div (Real.sqrt_pos.mpr h1).ne' (Real.sqrt_pos.mpr h2).ne', Real.log_sqrt h1.le,
        Real.log_sqrt h2.le]
      rfl
    rw [leviForm_congr heq, hSl z hz w hw]
    exact mul_nonneg (Nat.cast_nonneg m)
      (hsemi.2 (basePart₂ z) (oldPart_mem hz) (basePart₂ w) (tangent_old hP0 hw))
  · obtain ⟨c, hc⟩ := graph_prop hv hgen hz
    have hx := oldPart_mem hz
    have hsn : ∀ j, secNormAt y A m (v j) (basePart₂ z) = ‖val y A m (v j) (basePart₂ z)‖ :=
      fun j => secNormAt_eq (hv j) hx
    have hT : S (basePart₂ z) = ∑ j, secNormAt y A m (v j) (basePart₂ z) ^ 2 := hSv _ hx
    have hTpos : 0 < S (basePart₂ z) := hSp _ hx.1
    have hN : addedBlockNormSq z = ‖c‖ ^ 2 * S (basePart₂ z) := by
      rw [hT, Finset.mul_sum, addedBlockNormSq]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hcj : z ⟨none, j⟩ = c * val y A m (v j) (basePart₂ z) := hc j
      rw [hcj, norm_mul, mul_pow, hsn]
    have hB : (graphLine S hSp hSt N).h z = ‖c‖ := by
      show Real.sqrt (addedBlockNormSq z) / Real.sqrt (S (basePart₂ z)) = ‖c‖
      rw [hN, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_div_assoc,
        div_self (Real.sqrt_pos.mpr hTpos).ne', mul_one]
    rw [hB, hc j, norm_mul, hsn j, mul_comm]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
