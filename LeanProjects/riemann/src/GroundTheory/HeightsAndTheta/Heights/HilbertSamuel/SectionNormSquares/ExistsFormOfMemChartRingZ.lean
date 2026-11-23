import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionNormSqExtension

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

def IsRep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + n * a k) ∧
    aeval y g = s * aeval y h

theorem y_ne_zero {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {p : Σ k, ι k} (hp : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hX : (X p : MRing ι) ∈ mCoordIdeal y := by
    show X p ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  simpa using hz.2 _ hX

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

theorem val_eq {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h)
    (hh : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    val y A n s z = eval z (map (Int.castRingHom ℂ) g) /
      (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
  rw [eq_div_iff (mul_ne_zero hh (metric_ne hz n)), val_spec hs hz hr]
  ring

theorem rep_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s t : Ω} {g₁ h₁ g₂ h₂ : MRing ι}
    (r₁ : IsRep y a n s g₁ h₁) (r₂ : IsRep y a n t g₂ h₂) :
    IsRep y a n (s + t) (g₁ * h₂ + g₂ * h₁) (h₁ * h₂) := by
  obtain ⟨dg₁, dh₁, hg₁, hh₁, hd₁, hy₁⟩ := r₁
  obtain ⟨dg₂, dh₂, hg₂, hh₂, hd₂, hy₂⟩ := r₂
  refine ⟨dg₁ + dh₂, dh₁ + dh₂, homog_add (homog_mul hg₁ hh₂) (homog_congr (homog_mul hg₂ hh₁) fun k => ?_),
    homog_mul hh₁ hh₂, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    zify
    linear_combination hd₂ k - hd₁ k
  · simp only [Pi.add_apply]
    push_cast
    linear_combination hd₁ k
  · rw [map_add, map_mul, map_mul, map_mul, hy₁, hy₂]
    ring

def w (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) : chartLat y A.a n →+ (((Σ k, ι k) → ℂ) → ℂ) :=
  AddMonoidHom.mk' (fun s => val y A n s) fun s t => by
    funext z
    show val y A n ((s + t : chartLat y A.a n) : Ω) z = val y A n s z + val y A n t z
    by_cases hz : z ∈ mcPts (mCoordIdeal y)
    · obtain ⟨⟨g₁, h₁⟩, r₁, n₁⟩ := exists_rep_at s.2 hz
      obtain ⟨⟨g₂, h₂⟩, r₂, n₂⟩ := exists_rep_at t.2 hz
      have hT := metric_ne (A := A) hz n
      rw [AddSubgroup.coe_add, val_eq (add_mem s.2 t.2) hz (rep_add r₁ r₂) (by simpa using mul_ne_zero n₁ n₂),
        val_eq s.2 hz r₁ n₁, val_eq t.2 hz r₂ n₂]
      simp only [map_add, map_mul]
      field_simp
    · simp [val, hz]

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

theorem exists_chartData [DecidableEq K] (y : (Σ k, ι k) → Ω) (A : HermLine ι) (m N : ℕ) (v : Fin N → Ω)
    (hv : ∀ j, v j ∈ chartLat y A.a m) (c : ∀ k, ι k) :
    ∃ (d e : K → ℕ) (G : Fin N → MRing ι), (∀ k, (e k : ℤ) = d k + m * A.a k) ∧
      (∀ j, IsMultiHomog (G j) e) ∧ ∀ j, aeval y (G j) = v j * aeval y (chartMon c d) := by
  classical
  by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
  · choose Nn δ G hG hdeg hGv using fun j =>
      exists_chartForm y c hc (fun k => (m : ℤ) * A.a k) (hv j c hc)
    have hN : ∀ j k, Nn j k ≤ ∑ i, Nn i k := fun j k =>
      Finset.single_le_sum (f := fun i => Nn i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    set L : K → ℕ := fun k => ∑ i, Nn i k + ((m : ℤ) * A.a k).natAbs with hL
    refine ⟨L, fun k => ((L k : ℤ) + m * A.a k).toNat, fun j => G j * chartMon c (L - Nn j), fun k => ?_,
      fun j => homog_congr (homog_mul (hG j) (homog_chartMon c _)) fun k => ?_, fun j => ?_⟩
    · simp only [hL]
      generalize ∑ i, Nn i k = S
      generalize (m : ℤ) * A.a k = q
      omega
    · have h1 := hdeg j k
      have h2 := hN j k
      simp only [Pi.add_apply, Pi.sub_apply, hL]
      generalize (m : ℤ) * A.a k = q at *
      generalize ∑ i, Nn i k = S at *
      omega
    · rw [map_mul, hGv j, aeval_chartMon, aeval_chartMon, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← pow_add, Pi.sub_apply]
      congr 1
      have h2 := hN j k
      simp only [hL]
      omega
  · push Not at hc
    obtain ⟨k0, hk0⟩ := hc
    refine ⟨fun k => 1 + ((m : ℤ) * A.a k).natAbs, fun k => (((1 + ((m : ℤ) * A.a k).natAbs : ℕ) : ℤ) +
      m * A.a k).toNat, fun _ => 0, fun k => ?_, fun _ => homog_zero _, fun j => ?_⟩
    · dsimp only
      generalize (m : ℤ) * A.a k = q
      omega
    · rw [aeval_chartMon, Finset.prod_eq_zero (Finset.mem_univ k0) (by rw [hk0]; simp)]
      simp

def blockDeg (μ : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, μ ⟨k, i⟩

open Classical in

def comp (g : MRing ι) (δ : K → ℕ) : MRing ι :=
  ∑ μ ∈ g.support.filter (fun μ => blockDeg μ = δ), monomial μ (coeff μ g)

theorem homog_comp (g : MRing ι) (δ : K → ℕ) : IsMultiHomog (comp g δ) δ := by
  classical
  intro μ hμ k
  obtain ⟨ν, hν, hμν⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hμ)
  have h1 := MvPolynomial.support_monomial_subset hμν
  rw [Finset.mem_singleton] at h1
  subst h1
  exact congrFun (Finset.mem_filter.mp hν).2 k

theorem sum_comp (g : MRing ι) : ∑ δ ∈ g.support.image blockDeg, comp g δ = g := by
  classical
  unfold comp
  rw [Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem _ hμ)]
  exact g.as_sum.symm

theorem comp_eq_zero {g : MRing ι} {δ : K → ℕ} (hδ : δ ∉ g.support.image blockDeg) : comp g δ = 0 := by
  classical
  unfold comp
  refine Finset.sum_eq_zero fun μ hμ => ?_
  exact absurd (Finset.mem_image.mpr ⟨μ, (Finset.mem_filter.mp hμ).1, (Finset.mem_filter.mp hμ).2⟩) hδ

theorem prod_X_pow_eq_monomial' (δ : K → ℕ) :
    (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ δ k) = monomial (Finsupp.equivFunOnFinite.symm δ) 1 := by
  classical
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  symm
  rw [Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_]
  · rfl
  · have h1 : (Finsupp.equivFunOnFinite.symm δ) k = 0 := Finsupp.notMem_support_iff.mp hk
    rw [h1, pow_zero]

theorem comp_mem {y : (Σ k, ι k) → Ω} {g : MRing ι} (hg : g ∈ mCoordIdeal y) (δ : K → ℕ) :
    comp g δ ∈ mCoordIdeal y := by
  classical
  show comp g δ ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_homog y (homog_comp g δ)]
  suffices aeval y (comp g δ) = 0 by rw [this]; simp
  by_cases hδ : δ ∈ g.support.image blockDeg
  · have h0 : mConeMap y g = 0 := hg
    rw [← sum_comp g, map_sum] at h0
    have h1 : ∀ δ' ∈ g.support.image blockDeg, mConeMap y (comp g δ') =
        MvPolynomial.C (aeval y (comp g δ')) * monomial (Finsupp.equivFunOnFinite.symm δ') 1 := fun δ' _ => by
      erw [mConeMap_homog y (homog_comp g δ'), prod_X_pow_eq_monomial']
    rw [Finset.sum_congr rfl h1] at h0
    have h2 := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm δ)) h0
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at h2
    simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, mul_ite, mul_one, mul_zero,
      EmbeddingLike.apply_eq_iff_eq] at h2
    rw [Finset.sum_ite_eq' _ _ _, if_pos hδ] at h2
    exact h2
  · rw [comp_eq_zero hδ, map_zero]

theorem exists_gens (y : (Σ k, ι k) → Ω) :
    ∃ F : Finset (MRing ι × (K → ℕ)), (∀ p ∈ F, IsMultiHomog p.1 p.2 ∧ p.1 ∈ mCoordIdeal y) ∧
      mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (mCoordIdeal y) : (mCoordIdeal y).FG)
  refine ⟨s.biUnion fun g => (g.support.image blockDeg).image fun δ => (comp g δ, δ), ?_, ?_⟩
  · intro p hp
    obtain ⟨g, hg, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨homog_comp g δ, comp_mem ?_ δ⟩
    rw [← hs]
    exact Submodule.subset_span hg
  · rw [← hs]
    refine Submodule.span_le.mpr fun g hg => ?_
    rw [← sum_comp g]
    refine Ideal.sum_mem _ fun δ hδ => Ideal.subset_span ⟨(comp g δ, δ), ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image_of_mem _ hδ⟩

theorem mem_mcPts_of_gens {y : (Σ k, ι k) → Ω} {F : Finset (MRing ι × (K → ℕ))}
    (hF : mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))))
    {x : (Σ k, ι k) → ℂ} (hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0)
    (h0 : ∀ p ∈ F, eval x (map (Int.castRingHom ℂ) p.1) = 0) : x ∈ mcPts (mCoordIdeal y) := by
  refine ⟨hx, fun f hf => ?_⟩
  have hle : Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))) ≤
      RingHom.ker ((eval x).comp (map (Int.castRingHom ℂ))) := by
    rw [Ideal.span_le]
    rintro _ ⟨p, hp, rfl⟩
    simpa [RingHom.mem_ker] using h0 p hp
  simpa [RingHom.mem_ker] using hle (hF hf)

theorem norm_eval_rep {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a m)
    {c : ∀ k, ι k} {d e : K → ℕ} {G : MRing ι} (he : ∀ k, (e k : ℤ) = d k + m * A.a k) (hG : IsMultiHomog G e)
    (hGy : aeval y G = s * aeval y (chartMon c d)) {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) :
    ‖eval x (map (Int.castRingHom ℂ) G)‖ =
      secNormAt y A m s x * ‖eval x (map (Int.castRingHom ℂ) (chartMon c d))‖ * A.h x ^ m := by
  rw [secNormAt_eq hs hx, val_spec hs hx ⟨e, d, hG, homog_chartMon c d, he, hGy⟩, norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg (A.pos x hx.1).le]

theorem exists_G_ne {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m N : ℕ} {v : Fin N → Ω}
    (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v) {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {d e : K → ℕ} {G : Fin N → MRing ι} (he : ∀ k, (e k : ℤ) = d k + m * A.a k)
    (hG : ∀ j, IsMultiHomog (G j) e) (hGy : ∀ j, aeval y (G j) = v j * aeval y (chartMon c d))
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) (hxc : ∀ k, x ⟨k, c k⟩ ≠ 0) :
    ∃ j, eval x (map (Int.castRingHom ℂ) (G j)) ≠ 0 := by
  obtain ⟨u, hu, hsum⟩ := hgen c hc
  simp only [] at hsum
  choose δ U hU hUy using fun j => exists_form_of_mem_chartRingZ y c hc (hu j)
  have hδ : ∀ j k, δ j k ≤ ∑ i, δ i k := fun j k =>
    Finset.single_le_sum (f := fun i => δ i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set L : K → ℕ := fun k => ∑ i, δ i k with hL
  set F : MRing ι := ∑ j, U j * chartMon c (L - δ j) * G j - chartMon c (L + e) with hF
  have hFh : IsMultiHomog F (L + e) := by
    refine homog_sub (homog_sum _ fun j _ => homog_congr (homog_mul (homog_mul (hU j) (homog_chartMon c _))
      (hG j)) fun k => ?_) (homog_chartMon c _)
    have := hδ j k
    simp only [Pi.add_apply, Pi.sub_apply, hL] at this ⊢
    omega
  have hpow : ∀ k, y ⟨k, c k⟩ ^ (L k + e k) * y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k)) =
      y ⟨k, c k⟩ ^ (L k + d k) := by
    intro k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    push_cast
    linarith [he k]
  have e1 : ∀ j, aeval y (U j * chartMon c (L - δ j) * G j) =
      (u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k)))) * ∏ k, y ⟨k, c k⟩ ^ (L k + e k) := by
    intro j
    rw [map_mul, map_mul, hUy j, hGy j, aeval_chartMon, aeval_chartMon]
    have h3 : ∀ k, y ⟨k, c k⟩ ^ δ j k * y ⟨k, c k⟩ ^ (L - δ j) k * y ⟨k, c k⟩ ^ d k =
        y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k)) * y ⟨k, c k⟩ ^ (L k + e k) := by
      intro k
      rw [mul_comm (y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))), hpow k, ← pow_add, ← pow_add]
      congr 1
      have := hδ j k
      simp only [Pi.sub_apply, hL] at this ⊢
      omega
    calc _ = u j * v j * ∏ k, (y ⟨k, c k⟩ ^ δ j k * y ⟨k, c k⟩ ^ (L - δ j) k * y ⟨k, c k⟩ ^ d k) := by
          simp only [Finset.prod_mul_distrib]
          ring
      _ = _ := by
          rw [Finset.prod_congr rfl fun k _ => h3 k, Finset.prod_mul_distrib]
          ring
  have hFy : aeval y F = 0 := by
    rw [hF, map_sub, map_sum, Finset.sum_congr rfl fun j _ => e1 j, ← Finset.sum_mul, hsum, one_mul,
      aeval_chartMon]
    simp only [Pi.add_apply, sub_self]
  have hFx := vanish hx hFh hFy
  by_contra hne
  push Not at hne
  rw [hF] at hFx
  simp only [map_sub, map_sum, map_mul, hne, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero,
    eval_chartMon] at hFx
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hxc k)) hFx

end SectionNormSqExtension

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
