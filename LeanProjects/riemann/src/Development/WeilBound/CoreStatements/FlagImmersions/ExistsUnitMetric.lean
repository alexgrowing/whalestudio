import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariantStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

namespace RootFieldNumerics.RF.Smooth

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem evC_eq (w : (Σ k, J k) → ℂ) (f : MRing J) : evC w f = aeval w f := by
  rw [evC, MvPolynomial.eval_map, aeval_def, algebraMap_int_eq]

theorem evC_mul (w : (Σ k, J k) → ℂ) (f g : MRing J) : evC w (f * g) = evC w f * evC w g := by
  simp only [evC, map_mul]

theorem evC_conj (w : (Σ k, J k) → ℂ) (f : MRing J) :
    evC (fun p => (starRingEnd ℂ) (w p)) f = (starRingEnd ℂ) (evC w f) := by
  simp only [evC, MvPolynomial.eval_map]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  simp [map_sum, map_prod, map_pow, map_mul]

theorem contDiff_evC (f : MRing J) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun w : (Σ k, J k) → ℂ => evC w f := by
  simp only [evC_eq]
  induction f using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℝ ℂ i)

def blk (k : K) (w : (Σ k, J k) → ℂ) : ℝ := ∑ i, ‖w ⟨k, i⟩‖ ^ 2

theorem blk_pos {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) : 0 < blk k w := by
  obtain ⟨i, hi⟩ := hw k
  exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩

theorem blk_smul (c : K → ℂ) (w : (Σ k, J k) → ℂ) (k : K) :
    blk k (fun p => c p.1 * w p) = ‖c k‖ ^ 2 * blk k w := by
  simp [blk, norm_mul, mul_pow, Finset.mul_sum]

theorem blk_conj (w : (Σ k, J k) → ℂ) (k : K) : blk k (fun p => (starRingEnd ℂ) (w p)) = blk k w := by
  simp [blk]

theorem contDiff_blk (k : K) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (blk (J := J) k) := by
  unfold blk
  exact ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, J k))

def nu (f : MRing J) (d : K → ℕ) (w : (Σ k, J k) → ℂ) : ℝ := ‖evC w f‖ ^ 2 / ∏ k, blk k w ^ d k

private theorem evC_smul_lemma {f : MRing J} {d : K → ℕ} (hf : IsMultiHomog f d) (c : K → ℂ)
    (w : (Σ k, J k) → ℂ) : evC (fun p => c p.1 * w p) f = (∏ k, c k ^ d k) * evC w f := by
  simp only [evC, MvPolynomial.eval_map]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have key : ∏ p : (Σ k, J k), (c p.1 * w p) ^ m p = (∏ k, c k ^ d k) * ∏ p, w p ^ m p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ i : J k, c k ^ m ⟨k, i⟩ = c k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [key]
  ring

theorem nu_smul {f : MRing J} {d : K → ℕ} (hf : IsMultiHomog f d) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (w : (Σ k, J k) → ℂ) : nu f d (fun p => c p.1 * w p) = nu f d w := by
  unfold nu
  rw [evC_smul_lemma hf, norm_mul, mul_pow]
  simp_rw [blk_smul, mul_pow, Finset.prod_mul_distrib]
  have h1 : ‖∏ k, c k ^ d k‖ ^ 2 = ∏ k, (‖c k‖ ^ 2) ^ d k := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, ← pow_mul, ← pow_mul, mul_comm]
  have h2 : ∏ k, (‖c k‖ ^ 2) ^ d k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))
  rw [h1, mul_div_mul_left _ _ h2]

theorem nu_conj (f : MRing J) (d : K → ℕ) (w : (Σ k, J k) → ℂ) :
    nu f d (fun p => (starRingEnd ℂ) (w p)) = nu f d w := by
  simp only [nu, evC_conj, blk_conj, Complex.norm_conj]

theorem nu_nonneg (f : MRing J) (d : K → ℕ) {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : 0 ≤ nu f d w :=
  div_nonneg (by positivity) (Finset.prod_pos fun k _ => pow_pos (blk_pos hw k) _).le

theorem nu_pos {f : MRing J} (d : K → ℕ) {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (h : evC w f ≠ 0) :
    0 < nu f d w := by
  unfold nu
  exact div_pos (pow_pos (norm_pos_iff.2 h) 2) (Finset.prod_pos fun k _ => pow_pos (blk_pos hw k) _)

theorem contDiffOn_nu (f : MRing J) (d : K → ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (nu f d) {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun w : (Σ k, J k) → ℂ => ‖evC w f‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_evC f)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun w : (Σ k, J k) → ℂ => ∏ k, blk k w ^ d k :=
    contDiff_prod fun k _ => (contDiff_blk k).pow _
  exact h1.contDiffOn.div h2.contDiffOn fun w hw =>
    (Finset.prod_pos fun k _ => pow_pos (blk_pos hw k) _).ne'

theorem exists_finset {T : Type} (z : T → (Σ k, J k) → ℂ) (f : T → MRing J) (h : ∀ t, evC (z t) (f t) ≠ 0) :
    ∃ s : Finset T, ∀ t, ∃ t' ∈ s, evC (z t) (f t') ≠ 0 := by
  classical
  have hc : IsCompactElement (⨆ t, Ideal.span {f t}) :=
    (Submodule.fg_iff_compact _).1 (IsNoetherian.noetherian _)
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc
    (fun t => Ideal.span {f t}) le_rfl
  refine ⟨s, fun t => ?_⟩
  by_contra hno
  push_neg at hno
  let φ : MRing J →+* ℂ := (MvPolynomial.eval (z t)).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hle : (⨆ t' ∈ s, Ideal.span {f t'}) ≤ RingHom.ker φ :=
    iSup₂_le fun t' ht' => (Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.2 (hno t' ht'))
  have hmem : f t ∈ RingHom.ker φ :=
    hle (hs (Ideal.mem_iSup_of_mem t (Ideal.mem_span_singleton_self _)))
  exact h t (RingHom.mem_ker.1 hmem)

variable {Ω : Type} [Field Ω]

def Pres (y : (Σ k, J k) → Ω) (a : K → ℤ) (c₀ : Ω) (g h : MRing J) (dg dh : K → ℕ) : Prop :=
  IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) - dh k = a k) ∧ aeval y g = c₀ * aeval y h

theorem cross {y : (Σ k, J k) → Ω} {a : K → ℤ} {c₀ : Ω} {g h g' h' : MRing J} {dg dh dg' dh' : K → ℕ}
    (H : Pres y a c₀ g h dg dh) (H' : Pres y a c₀ g' h' dg' dh') {w : (Σ k, J k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal y)) : evC w g * evC w h' = evC w g' * evC w h := by
  obtain ⟨hg, hh, hgh, hy⟩ := H
  obtain ⟨hg', hh', hgh', hy'⟩ := H'
  have hdeg : ∀ k, dg k + dh' k = dg' k + dh k := fun k => by
    have h1 := hgh k
    have h2 := hgh' k
    omega
  have hP : (∏ k, (X k : MvPolynomial K Ω) ^ dg k) * ∏ k, X k ^ dh' k =
      (∏ k, X k ^ dg' k) * ∏ k, X k ^ dh k := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp_rw [← pow_add, hdeg]
  have hmem : g * h' - g' * h ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, mConeMap_homog y hg,
      mConeMap_homog y hh', mConeMap_homog y hg', mConeMap_homog y hh, hy, hy', sub_eq_zero]
    simp only [map_mul]
    linear_combination (C c₀ * C ((aeval y) h) * C ((aeval y) h')) * hP
  have h0 := hw.2 _ hmem
  have h1 : evC w (g * h' - g' * h) = 0 := h0
  simp only [evC, map_sub, map_mul] at h1 ⊢
  exact sub_eq_zero.1 h1

private theorem sq_zpow_lemma_4 (x : ℝ) (hx : x ≠ 0) (n : ℤ) :
    (x ^ 2) ^ n.toNat / (x ^ 2) ^ (-n).toNat = (x ^ n) ^ 2 := by
  rcases le_total 0 n with h0 | h0
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have : (-(m : ℤ)).toNat = 0 := by omega
    rw [this, Int.toNat_natCast, zpow_natCast, pow_zero, div_one, ← pow_mul, ← pow_mul, mul_comm]
  · obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat h0
    subst hm
    have : (-(m : ℤ)).toNat = 0 := by omega
    rw [this, neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast, pow_zero, one_div, inv_pow,
      ← pow_mul, ← pow_mul, mul_comm]

theorem exists_unit_metric (y : (Σ k, J k) → Ω) (a : K → ℤ) (c₀ : Ω)
    (hloc : ∀ w : (Σ k, J k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
      ∃ g h dg dh, Pres y a c₀ g h dg dh ∧ evC w g ≠ 0 ∧ evC w h ≠ 0) :
    ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧
      ∀ w ∈ mcPts (mCoordIdeal y), ∀ g h dg dh, Pres y a c₀ g h dg dh → ‖evC w g‖ = A.h w * ‖evC w h‖ := by
  classical
  choose g h dg dh hP hg hh using
    fun w : {w : (Σ k, J k) → ℂ // ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} => hloc w.1 w.2
  obtain ⟨s, hs⟩ := exists_finset (fun w : {w : (Σ k, J k) → ℂ // ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} => w.1)
    (fun t => g t * h t) (fun t => by rw [evC_mul]; exact mul_ne_zero (hg t) (hh t))
  obtain ⟨N, hN⟩ : ∃ N : ((Σ k, J k) → ℂ) → ℝ,
      N = fun w => ∑ t ∈ s, nu (g t) (dg t) w * nu (h t) (dh t) w := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ((Σ k, J k) → ℂ) → ℝ,
      D = fun w => ∑ t ∈ s, nu (h t) (dh t) w ^ 2 := ⟨_, rfl⟩
  obtain ⟨Zp, hZp⟩ : ∃ Zp : ((Σ k, J k) → ℂ) → ℝ,
      Zp = fun w => ∏ k, blk k w ^ (a k).toNat := ⟨_, rfl⟩
  obtain ⟨Zm, hZm⟩ : ∃ Zm : ((Σ k, J k) → ℂ) → ℝ,
      Zm = fun w => ∏ k, blk k w ^ (-a k).toNat := ⟨_, rfl⟩
  have hpos : ∀ w : (Σ k, J k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
      0 < N w ∧ 0 < D w ∧ 0 < Zp w ∧ 0 < Zm w := by
    intro w hw
    obtain ⟨t, ht, hne⟩ := hs ⟨w, hw⟩
    rw [evC_mul] at hne
    have hgt := left_ne_zero_of_mul hne
    have hht := right_ne_zero_of_mul hne
    subst hN hD hZp hZm
    refine ⟨?_, ?_, Finset.prod_pos fun k _ => pow_pos (blk_pos hw k) _,
      Finset.prod_pos fun k _ => pow_pos (blk_pos hw k) _⟩
    · exact Finset.sum_pos' (fun t _ => mul_nonneg (nu_nonneg _ _ hw) (nu_nonneg _ _ hw))
        ⟨t, ht, mul_pos (nu_pos _ hw hgt) (nu_pos _ hw hht)⟩
    · exact Finset.sum_pos' (fun t _ => sq_nonneg _) ⟨t, ht, pow_pos (nu_pos _ hw hht) 2⟩
  have hsmul : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) →
      Real.sqrt (N (fun p => c p.1 * z p) * Zp (fun p => c p.1 * z p) /
        (D (fun p => c p.1 * z p) * Zm (fun p => c p.1 * z p))) =
      (∏ k, ‖c k‖ ^ a k) * Real.sqrt (N z * Zp z / (D z * Zm z)) := by
    intro c z hc
    have hN' : N (fun p => c p.1 * z p) = N z := by
      subst hN
      exact Finset.sum_congr rfl fun t _ => by
        rw [nu_smul (hP t).1 c hc, nu_smul (hP t).2.1 c hc]
    have hD' : D (fun p => c p.1 * z p) = D z := by
      subst hD
      exact Finset.sum_congr rfl fun t _ => by rw [nu_smul (hP t).2.1 c hc]
    have hZp' : Zp (fun p => c p.1 * z p) = (∏ k, (‖c k‖ ^ 2) ^ (a k).toNat) * Zp z := by
      subst hZp
      simp only [blk_smul, mul_pow, Finset.prod_mul_distrib]
    have hZm' : Zm (fun p => c p.1 * z p) = (∏ k, (‖c k‖ ^ 2) ^ (-a k).toNat) * Zm z := by
      subst hZm
      simp only [blk_smul, mul_pow, Finset.prod_mul_distrib]
    have hu : (∏ k, (‖c k‖ ^ 2) ^ (a k).toNat) / ∏ k, (‖c k‖ ^ 2) ^ (-a k).toNat =
        (∏ k, ‖c k‖ ^ a k) ^ 2 := by
      rw [← Finset.prod_div_distrib, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun k _ => sq_zpow_lemma_4 _ (norm_ne_zero_iff.2 (hc k)) _
    rw [hN', hD', hZp', hZm']
    have e1 : N z * ((∏ k, (‖c k‖ ^ 2) ^ (a k).toNat) * Zp z) /
        (D z * ((∏ k, (‖c k‖ ^ 2) ^ (-a k).toNat) * Zm z)) =
        ((∏ k, (‖c k‖ ^ 2) ^ (a k).toNat) / ∏ k, (‖c k‖ ^ 2) ^ (-a k).toNat) *
          (N z * Zp z / (D z * Zm z)) := by ring
    rw [e1, hu, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _)]
  have hconj : ∀ z : (Σ k, J k) → ℂ,
      Real.sqrt (N (fun p => (starRingEnd ℂ) (z p)) * Zp (fun p => (starRingEnd ℂ) (z p)) /
        (D (fun p => (starRingEnd ℂ) (z p)) * Zm (fun p => (starRingEnd ℂ) (z p)))) =
      Real.sqrt (N z * Zp z / (D z * Zm z)) := by
    intro z
    subst hN hD hZp hZm
    simp only [nu_conj, blk_conj]
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => Real.sqrt (N w * Zp w / (D w * Zm w))) {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
    have cN : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) N {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
      subst hN
      exact ContDiffOn.sum fun t _ => (contDiffOn_nu _ _).mul (contDiffOn_nu _ _)
    have cD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
      subst hD
      exact ContDiffOn.sum fun t _ => (contDiffOn_nu _ _).pow 2
    have cZp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Zp {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
      subst hZp
      exact (contDiff_prod fun k _ => (contDiff_blk k).pow _).contDiffOn
    have cZm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Zm {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
      subst hZm
      exact (contDiff_prod fun k _ => (contDiff_blk k).pow _).contDiffOn
    refine ((cN.mul cZp).div (cD.mul cZm) fun w hw =>
      (mul_pos (hpos w hw).2.1 (hpos w hw).2.2.2).ne').sqrt fun w hw => ?_
    have := hpos w hw
    exact (div_pos (mul_pos this.1 this.2.2.1) (mul_pos this.2.1 this.2.2.2)).ne'
  refine ⟨⟨a, fun w => Real.sqrt (N w * Zp w / (D w * Zm w)), fun z hz => ?_,
    fun c z hc => hsmul c z hc⟩, rfl, hsm, hconj, ?_⟩
  · have := hpos z hz
    exact Real.sqrt_pos.2 (div_pos (mul_pos this.1 this.2.2.1) (mul_pos this.2.1 this.2.2.2))
  intro w hw g0 h0 dg0 dh0 H0
  have hw1 := hw.1
  obtain ⟨t0, ht0, hne0⟩ := hs ⟨w, hw1⟩
  rw [evC_mul] at hne0
  have hht0 := right_ne_zero_of_mul hne0
  show ‖evC w g0‖ = Real.sqrt (N w * Zp w / (D w * Zm w)) * ‖evC w h0‖
  by_cases hz : evC w h0 = 0
  · have hc := cross H0 (hP ⟨w, hw1⟩) hw
    have hc0 := cross H0 (hP t0) hw
    rw [hz, mul_zero] at hc0
    have : evC w g0 = 0 := (mul_eq_zero.1 hc0).resolve_right hht0
    simp [this, hz]
  have hh0 : ‖evC w h0‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hr : ∀ t, ‖evC w (g t)‖ = ‖evC w g0‖ / ‖evC w h0‖ * ‖evC w (h t)‖ := by
    intro t
    have hc := congrArg norm (cross H0 (hP t) hw)
    simp only [norm_mul] at hc
    rw [div_mul_eq_mul_div, eq_div_iff hh0, ← hc]
  have hpw := hpos w hw1
  have hterm : ∀ t, nu (g t) (dg t) w * nu (h t) (dh t) w * Zp w =
      (‖evC w g0‖ / ‖evC w h0‖) ^ 2 * Zm w * nu (h t) (dh t) w ^ 2 := by
    intro t
    have hdeg : (∏ k, blk k w ^ dg t k) = (∏ k, blk k w ^ dh t k) * Zp w / Zm w := by
      rw [eq_div_iff hpw.2.2.2.ne']
      subst hZp hZm
      simp only [← Finset.prod_mul_distrib, ← pow_add]
      refine Finset.prod_congr rfl fun k _ => ?_
      congr 1
      have := (hP t).2.2.1 k
      omega
    have hB : (∏ k, blk k w ^ dh t k) ≠ 0 :=
      (Finset.prod_pos fun k _ => pow_pos (blk_pos hw1 k) _).ne'
    unfold nu
    rw [hr t, hdeg]
    have hZm0 := hpw.2.2.2.ne'
    have hZp0 := hpw.2.2.1.ne'
    field_simp
  have hND : N w * Zp w = (‖evC w g0‖ / ‖evC w h0‖) ^ 2 * Zm w * D w := by
    subst hN hD
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => hterm t
  rw [hND, show (‖evC w g0‖ / ‖evC w h0‖) ^ 2 * Zm w * D w / (D w * Zm w) =
      (‖evC w g0‖ / ‖evC w h0‖) ^ 2 by field_simp [hpw.2.1.ne', hpw.2.2.2.ne'],
    Real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _)), div_mul_cancel₀ _ hh0]

private theorem homog_mul_lemma_3 {p q : MRing J} {d1 d2 : K → ℕ} (hp : IsMultiHomog p d1)
    (hq : IsMultiHomog q d2) : IsMultiHomog (p * q) (d1 + d2) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hp m1 hm1 k, hq m2 hm2 k]

theorem pres_off {y : (Σ k, J k) → Ω} (hP : IsMultiHomogIdeal (mCoordIdeal y)) (a : K → ℤ) (c₀ : Ω)
    {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hn : w ∉ mcPts (mCoordIdeal y)) :
    ∃ g h dg dh, Pres y a c₀ g h dg dh ∧ evC w g ≠ 0 ∧ evC w h ≠ 0 := by
  classical
  have hne : ∃ f ∈ mCoordIdeal y, evC w f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hn ⟨hw, fun f hf => hc f hf⟩
  obtain ⟨S, hS, hPS⟩ := hP
  have hgen : ∃ s0 ∈ S, evC w s0 ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨f, hf, hfw⟩ := hne
    let φ : MRing J →+* ℂ := (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ))
    have hle : mCoordIdeal y ≤ RingHom.ker φ := by
      rw [hPS, Ideal.span_le]
      intro s hs
      exact RingHom.mem_ker.2 (hc s hs)
    exact hfw (RingHom.mem_ker.1 (hle hf))
  obtain ⟨s0, hs0S, hs0⟩ := hgen
  obtain ⟨e, he⟩ := hS s0 hs0S
  have hs0y : aeval y s0 = 0 := by
    have h1 : s0 ∈ mCoordIdeal y := hPS ▸ Ideal.subset_span hs0S
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap_homog y he] at h1
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ e k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact C_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hX)
  choose i hi using hw
  let mon : (K → ℕ) → MRing J := fun n =>
    monomial (Finsupp.equivFunOnFinite.symm fun p => if p.2 = i p.1 then n p.1 else 0) 1
  have hmon : ∀ n, IsMultiHomog (mon n) n := by
    intro n m hm k
    have hm' := MvPolynomial.support_monomial_subset hm
    rw [Finset.mem_singleton] at hm'
    subst hm'
    simp [Finset.sum_ite_eq']
  have hmonw : ∀ n, evC w (mon n) ≠ 0 := by
    intro n
    simp only [mon, evC, MvPolynomial.map_monomial, MvPolynomial.eval_monomial, map_one, one_mul]
    rw [Finsupp.prod]
    refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
    rcases p with ⟨k, j⟩
    have hj : j = i k := by
      by_contra hj
      simp [hj] at hp
    subst hj
    exact pow_ne_zero _ (hi k)
  clear_value mon
  refine ⟨s0 * mon (fun k => (a k).toNat), s0 * mon (fun k => (-a k).toNat),
    e + fun k => (a k).toNat, e + fun k => (-a k).toNat,
    ⟨homog_mul_lemma_3 he (hmon _), homog_mul_lemma_3 he (hmon _), fun k => ?_, ?_⟩, ?_, ?_⟩
  · show ((e k + (a k).toNat : ℕ) : ℤ) - ((e k + (-a k).toNat : ℕ) : ℤ) = a k
    push_cast
    omega
  · rw [map_mul, map_mul, hs0y, zero_mul, zero_mul, mul_zero]
  · rw [evC_mul]
    exact mul_ne_zero hs0 (hmonw _)
  · rw [evC_mul]
    exact mul_ne_zero hs0 (hmonw _)

end RootFieldNumerics.RF.Smooth
