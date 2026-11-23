import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockOldPartSurj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace PowerBlockOldPartSurj

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

theorem mem_of_homog {y : (Σ k, ι k) → Ω} {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
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

theorem exists_chart_at {y : (Σ k, ι k) → Ω} {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hx.1
  refine ⟨c, hc, fun k h0 => hc k ?_⟩
  have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
    show X _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  simpa using hx.2 _ hX

theorem exists_common_forms (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ)
    (m N : ℕ) (v : Fin N → Ω) (hv : ∀ j, v j ∈ chartLat y a m) :
    ∃ (L E : K → ℕ) (G : Fin N → MRing ι), (∀ j, IsMultiHomog (G j) E) ∧ (∀ k, (E k : ℤ) = m * a k + L k) ∧
      ∀ j, aeval y (G j) = v j * ∏ k, y ⟨k, c k⟩ ^ L k := by
  choose Nj δ G hG hdeg hGv using fun j => exists_chartForm y c hc (fun k => (m : ℤ) * a k) (hv j c hc)
  have hN : ∀ j k, Nj j k ≤ ∑ i, Nj i k := fun j k =>
    Finset.single_le_sum (f := fun i => Nj i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set L : K → ℕ := fun k => ∑ i, Nj i k + ((m : ℤ) * a k).natAbs with hL
  refine ⟨L, fun k => ((L k : ℤ) + m * a k).toNat, fun j => G j * chartMon c (L - Nj j),
    fun j => homog_congr (homog_mul (hG j) (homog_chartMon c _)) fun k => ?_, fun k => ?_, fun j => ?_⟩
  · have h1 := hdeg j k
    have h2 := hN j k
    simp only [Pi.add_apply, Pi.sub_apply, hL]
    generalize (m : ℤ) * a k = q at *
    generalize ∑ i, Nj i k = S at *
    omega
  · simp only [hL]
    generalize (m : ℤ) * a k = q
    generalize ∑ i, Nj i k = S
    omega
  · rw [map_mul, hGv j, aeval_chartMon, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add, Pi.sub_apply]
    congr 1
    have h2 := hN j k
    simp only [hL]
    omega

theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} {m N : ℕ}
    {v : Fin N → Ω} (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * a k) v) {L E : K → ℕ} {G : Fin N → MRing ι}
    (hG : ∀ j, IsMultiHomog (G j) E) (hE : ∀ k, (E k : ℤ) = m * a k + L k)
    (hGy : ∀ j, aeval y (G j) = v j * ∏ k, y ⟨k, c k⟩ ^ L k)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) (hxc : ∀ k, x ⟨k, c k⟩ ≠ 0) :
    ∃ j, eval x (map (Int.castRingHom ℂ) (G j)) ≠ 0 := by
  obtain ⟨u, hu, hsum⟩ := hgen c hc
  have hsum' : ∑ j, u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) = 1 := hsum
  choose ε U hU hUv using fun j => exists_form_of_mem_chartRingZ y c hc (hu j)
  have hle : ∀ j k, ε j k ≤ ∑ i, ε i k := fun j k =>
    Finset.single_le_sum (f := fun i => ε i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set Dt : K → ℕ := fun k => ∑ i, ε i k with hDt
  set Φ : MRing ι := ∑ j, U j * G j * chartMon c (fun k => Dt k - ε j k) - chartMon c (fun k => Dt k + E k)
    with hΦ
  have hΦh : IsMultiHomog Φ (fun k => Dt k + E k) :=
    homog_sub (homog_sum _ fun j _ => homog_congr (homog_mul (homog_mul (hU j) (hG j)) (homog_chartMon c _))
      fun k => by
        have := hle j k
        simp only [Pi.add_apply, hDt] at this ⊢
        omega) (homog_chartMon c _)
  have key : ∀ j, (∏ k, y ⟨k, c k⟩ ^ ε j k) * (∏ k, y ⟨k, c k⟩ ^ L k) * (∏ k, y ⟨k, c k⟩ ^ (Dt k - ε j k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (Dt k + E k) := by
    intro j
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    have h1 := hE k
    have h2 : ε j k ≤ Dt k := hle j k
    push_cast [Nat.cast_sub h2]
    linarith
  have hΦy : aeval y Φ = 0 := by
    rw [hΦ, map_sub, map_sum, aeval_chartMon, sub_eq_zero]
    calc ∑ j, aeval y (U j * G j * chartMon c (fun k => Dt k - ε j k))
        = ∑ j, u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (Dt k + E k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, map_mul, hUv j, hGy j, aeval_chartMon]
          calc (u j * ∏ k, y ⟨k, c k⟩ ^ ε j k) * (v j * ∏ k, y ⟨k, c k⟩ ^ L k) *
                ∏ k, y ⟨k, c k⟩ ^ (Dt k - ε j k)
              = u j * v j * ((∏ k, y ⟨k, c k⟩ ^ ε j k) * (∏ k, y ⟨k, c k⟩ ^ L k) *
                  ∏ k, y ⟨k, c k⟩ ^ (Dt k - ε j k)) := by ring
            _ = _ := by rw [key j]; ring
      _ = ∏ k, y ⟨k, c k⟩ ^ (Dt k + E k) := by rw [← Finset.sum_mul, hsum', one_mul]
  have hΦx := hx.2 Φ (mem_of_homog hΦh hΦy)
  by_contra hall
  simp only [not_exists, not_not] at hall
  simp only [hΦ, map_sub, map_sum, map_mul, eval_chartMon, hall, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_sub, neg_eq_zero] at hΦx
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hxc k)) hΦx

def substForms {N : ℕ} (G : Fin N → MRing ι) : (Σ k, addIdx ι N k) → MRing ι
  | ⟨none, j⟩ => G j
  | ⟨some k, i⟩ => X ⟨k, i⟩

theorem vanish_new {N : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin N → Ω) (E : K → ℕ) (ρ : Ω) (G : Fin N → MRing ι)
    (hG : ∀ j, IsMultiHomog (G j) E) (hGy : ∀ j, aeval y (G j) = v j * ρ)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) {f : MRing (addIdx ι N)}
    (hf : f ∈ mCoordIdeal (addBlock y v)) :
    eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) f) = 0 := by
  classical

  let Γ : MRing (addIdx ι N) →ₐ[ℤ] MvPolynomial (Option K) (MRing ι) :=
    aeval fun p => MvPolynomial.C (substForms G p) * MvPolynomial.X p.1

  let Θ : MvPolynomial (Option K) Ω →+* MvPolynomial (Option K) (MvPolynomial K Ω) :=
    eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun o => Option.elim o
      (MvPolynomial.C (MvPolynomial.C ρ * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ E k) * MvPolynomial.X none)
      fun k => MvPolynomial.C (MvPolynomial.X k) * MvPolynomial.X (some k)
  have hcomm : (MvPolynomial.map (mConeMap y).toRingHom).comp Γ.toRingHom =
      Θ.comp (mConeMap (addBlock y v)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int
        (((MvPolynomial.map (mConeMap y).toRingHom).comp Γ.toRingHom).comp C)
        ((Θ.comp (mConeMap (addBlock y v)).toRingHom).comp C)) r
    · obtain ⟨o, i⟩ := p
      cases o with
      | none =>
        change Fin N at i
        have hΓ : Γ (X ⟨none, i⟩) = MvPolynomial.C (G i) * MvPolynomial.X none := by
          simp only [Γ, aeval_X]
          rfl
        have hM : mConeMap (addBlock y v) (X ⟨none, i⟩) = MvPolynomial.C (v i) * MvPolynomial.X none := by
          simp only [mConeMap, aeval_X]
          rfl
        show MvPolynomial.map (mConeMap y).toRingHom (Γ (X ⟨none, i⟩)) = Θ (mConeMap (addBlock y v) (X ⟨none, i⟩))
        rw [hΓ, hM, map_mul, map_C, map_X, map_mul]
        have hC : ∀ w : Ω, Θ (MvPolynomial.C w) = MvPolynomial.C (MvPolynomial.C w) := fun w => eval₂Hom_C _ _ _
        have hX : Θ (MvPolynomial.X none) = MvPolynomial.C (MvPolynomial.C ρ *
            ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ E k) * MvPolynomial.X none := eval₂Hom_X' _ _ _
        rw [hC, hX, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, mConeMap_homog y (hG i), hGy i]
        simp only [map_mul]
        ring
      | some k =>
        have hΓ : Γ (X ⟨some k, i⟩) = MvPolynomial.C (X ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [Γ, aeval_X]
          rfl
        have hM : mConeMap (addBlock y v) (X ⟨some k, i⟩) = MvPolynomial.C (y ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [mConeMap, aeval_X]
          rfl
        show MvPolynomial.map (mConeMap y).toRingHom (Γ (X ⟨some k, i⟩)) =
          Θ (mConeMap (addBlock y v) (X ⟨some k, i⟩))
        rw [hΓ, hM, map_mul, map_C, map_X, map_mul]
        have hC : Θ (MvPolynomial.C (y ⟨k, i⟩)) = MvPolynomial.C (MvPolynomial.C (y ⟨k, i⟩)) := eval₂Hom_C _ _ _
        have hX : Θ (MvPolynomial.X (some k)) = MvPolynomial.C (MvPolynomial.X k) * MvPolynomial.X (some k) :=
          eval₂Hom_X' _ _ _
        have hY : (mConeMap y).toRingHom (X ⟨k, i⟩) = MvPolynomial.C (y ⟨k, i⟩) * MvPolynomial.X k := by
          simp [mConeMap]
        rw [hC, hX, hY, C_mul]
        ring
  have hzero : MvPolynomial.map (mConeMap y).toRingHom (Γ f) = 0 := by
    have h1 : MvPolynomial.map (mConeMap y).toRingHom (Γ f) = Θ (mConeMap (addBlock y v) f) :=
      RingHom.congr_fun hcomm f
    have h2 : mConeMap (addBlock y v) f = 0 := RingHom.mem_ker.mp hf
    rw [h1, h2, map_zero]

  let ψ : MRing ι →+* ℂ := (eval x).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hcoef : MvPolynomial.map ψ (Γ f) = 0 := by
    ext μ
    rw [coeff_map, coeff_zero]
    have hm : coeff μ (Γ f) ∈ mCoordIdeal y := by
      show _ ∈ RingHom.ker (mConeMap y)
      rw [RingHom.mem_ker]
      have := congrArg (coeff μ) hzero
      rwa [coeff_map, coeff_zero] at this
    exact hx.2 _ hm

  have hval : ((eval fun _ => (1 : ℂ)).comp ((MvPolynomial.map ψ).comp Γ.toRingHom)) =
      (eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)))).comp
        (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int
        (((eval fun _ => (1 : ℂ)).comp ((MvPolynomial.map ψ).comp Γ.toRingHom)).comp C)
        (((eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)))).comp
          (MvPolynomial.map (Int.castRingHom ℂ))).comp C)) r
    · obtain ⟨o, i⟩ := p
      cases o with
      | none =>
        change Fin N at i
        have hΓ : Γ (X ⟨none, i⟩) = MvPolynomial.C (G i) * MvPolynomial.X none := by
          simp only [Γ, aeval_X]
          rfl
        show eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ (X ⟨none, i⟩))) =
          eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) (X ⟨none, i⟩))
        rw [hΓ, map_mul, map_C, map_X, map_X, eval_X, map_mul, eval_C, eval_X, mul_one]
        rfl
      | some k =>
        have hΓ : Γ (X ⟨some k, i⟩) = MvPolynomial.C (X ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [Γ, aeval_X]
          rfl
        show eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ (X ⟨some k, i⟩))) =
          eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) (X ⟨some k, i⟩))
        rw [hΓ, map_mul, map_C, map_X, map_X, eval_X, map_mul, eval_C, eval_X, mul_one]
        simp [ψ]
        rfl
  have h3 : eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ f)) =
      eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) f) :=
    RingHom.congr_fun hval f
  rw [← h3, hcoef, map_zero]

end PowerBlockOldPartSurj

open PowerBlockOldPartSurj in

theorem PowerBlockOldPartSurj.proof : PowerBlockOldPartSurj.Statement := by
  intro K _ ι _ Ω _ y a m N v hv hgen x hx
  classical
  obtain ⟨c, hxc, hyc⟩ := exists_chart_at hx
  obtain ⟨L, E, G, hG, hE, hGy⟩ := exists_common_forms y c hyc a m N v hv
  obtain ⟨j, hj⟩ := exists_ne_zero hyc hgen hG hE hGy hx hxc
  refine ⟨addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)), ⟨fun k => ?_, fun f hf => ?_⟩, rfl⟩
  · cases k with
    | none => exact ⟨j, hj⟩
    | some k => exact ⟨c k, hxc k⟩
  · exact vanish_new y v E _ G hG hGy hx hf

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
