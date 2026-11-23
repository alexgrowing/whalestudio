import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace SupBoundCount

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem continuousOn_lift (d : HSMBlockDatum D K ι Ω) (x₀ : d.R.X) :
    ContinuousOn (d.R.lift x₀) (d.R.U x₀) := by
  intro y hy
  refine (continuousAt_pi.2 fun p => ?_).continuousWithinAt
  obtain ⟨j, hj⟩ := d.R.A.cover y
  have hpt : d.R.A.chart j y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x₀ :=
    ⟨(d.R.A.chart j).map_source hj, by simpa [(d.R.A.chart j).left_inv hj] using hy⟩
  have han := d.R.holo x₀ p j _ hpt
  have h2 : ContinuousAt ((fun y => d.R.lift x₀ y p) ∘ (d.R.A.chart j).symm ∘ d.R.A.chart j) y :=
    han.continuousAt.comp ((d.R.A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(d.R.A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(d.R.A.chart j).left_inv hy']

theorem continuous_blockPt {β : Type*} [TopologicalSpace β] (d : HSMBlockDatum D K ι Ω)
    {Φ : ((Σ k, ι k) → ℂ) → β} (hc : ContinuousOn Φ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → Φ (fun p => c p.1 * z p) = Φ z) :
    Continuous fun x => Φ (blockPt d x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (d.R.isOpen_U x₀).mem_nhds (d.R.mem_U x₀)
  have h1 : ContinuousAt (d.R.lift x₀) x₀ := (continuousOn_lift d x₀).continuousAt hU
  have h0 : d.R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (d.R.mem x₀ x₀ (d.R.mem_U x₀)).1
  have h2 : ContinuousAt (fun x => Φ (d.R.lift x₀ x)) x₀ :=
    (hc.continuousAt (SupBoundBlock.isOpen_blockNonzero.mem_nhds h0)).comp h1
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  obtain ⟨c, hc0, he⟩ := d.R.compat x x₀ x ⟨d.R.mem_U x, hx⟩
  show Φ (d.R.lift x₀ x) = Φ (d.R.lift x x)
  rw [he, hinv c _ hc0]

theorem conjPt_torus (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    conjPt (fun p => c p.1 * z p) = fun p => starRingEnd ℂ (c p.1) * conjPt z p := by
  funext p
  simp [conjPt]

theorem conjPt_blockNonzero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, conjPt z ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, by simpa [conjPt] using hi⟩

theorem continuous_conjPt' : Continuous (conjPt : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) :=
  continuous_pi fun p => Complex.continuous_conj.comp (continuous_apply p)

theorem continuous_conj_blockPt {β : Type*} [TopologicalSpace β] (d : HSMBlockDatum D K ι Ω)
    {Φ : ((Σ k, ι k) → ℂ) → β} (hc : ContinuousOn Φ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → Φ (fun p => c p.1 * z p) = Φ z) :
    Continuous fun x => Φ (conjPt (blockPt d x)) :=
  continuous_blockPt d (Φ := fun z => Φ (conjPt z))
    (hc.comp continuous_conjPt'.continuousOn fun _ hz => conjPt_blockNonzero hz)
    fun c z hc0 => by rw [conjPt_torus, hinv _ _ fun k => (map_ne_zero _).2 (hc0 k)]

theorem integrable_blockPt {E : Type*} [NormedAddCommGroup E] (d : HSMBlockDatum D K ι Ω)
    {Φ : ((Σ k, ι k) → ℂ) → E} (hc : ContinuousOn Φ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → Φ (fun p => c p.1 * z p) = Φ z) :
    Integrable (fun x => Φ (blockPt d x)) d.dV ∧ Integrable (fun x => Φ (conjPt (blockPt d x))) d.dV := by
  have := d.vol.1
  exact ⟨integrableOn_univ.1 ((continuous_blockPt d hc hinv).continuousOn.integrableOn_compact isCompact_univ),
    integrableOn_univ.1 ((continuous_conj_blockPt d hc hinv).continuousOn.integrableOn_compact isCompact_univ)⟩

theorem eval_conjPt (f : MRing ι) (z : (Σ k, ι k) → ℂ) :
    eval (conjPt z) (map (Int.castRingHom ℂ) f) = starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  have : (starRingEnd ℂ).comp ((eval z).comp (map (Int.castRingHom ℂ))) =
      (eval (conjPt z)).comp (map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_) <;> simp [conjPt]
  exact (RingHom.congr_fun this f).symm

theorem conjPt_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    conjPt z ∈ mcPts P :=
  ⟨conjPt_blockNonzero hz.1, fun f hf => by rw [eval_conjPt, hz.2 f hf, map_zero]⟩

theorem blockPt_mem (d : HSMBlockDatum D K ι Ω) (x : d.R.X) : blockPt d x ∈ mcPts (mCoordIdeal d.y) :=
  d.R.mem x x (d.R.mem_U x)

theorem eval_map_int_rat (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval z (map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f)) = eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.map_map]
  congr 2

theorem h_continuousOn (d : HSMBlockDatum D K ι Ω) : ContinuousOn d.A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  d.semipos.1.continuousOn

theorem prod_unitDeg (c : K → ℂ) (k₀ : K) : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
  rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
  simp [unitDeg]

theorem ratio_continuousOn (d : HSMBlockDatum D K ι Ω) (f : MRing ι) (n : ℕ) :
    ContinuousOn (fun z => ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousOn.div ((h_continuousOn d).pow n)
    fun z hz => pow_ne_zero _ (d.A.pos z hz).ne'

theorem ratio_torus (d : HSMBlockDatum D K ι Ω) {f : MRing ι} {n : ℕ} (hf : IsMultiHomog f (blockDeg d.k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    ‖eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f)‖ / d.A.h (fun p => c p.1 * z p) ^ n =
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n :=
  SupBoundBlock.normRatio_torus hf d.A d.deg ⟨c, hc, rfl⟩

def pairRe (A : HermLine ι) (n : ℕ) (f f' : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ((eval z (map (Int.castRingHom ℂ) f)).re * (eval z (map (Int.castRingHom ℂ) f')).re +
    (eval z (map (Int.castRingHom ℂ) f)).im * (eval z (map (Int.castRingHom ℂ) f')).im) / A.h z ^ (2 * n)

theorem pairValH_re (A : HermLine ι) (n : ℕ) (f f' : MRing ι) (z : (Σ k, ι k) → ℂ) :
    (pairValH A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') z).re = pairRe A n f f' z := by
  simp only [pairValH, eval_map_int_rat, pairRe, Complex.div_ofReal_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

theorem pairValH_torus (d : HSMBlockDatum D K ι Ω) {n : ℕ} {f f' : MRing ι}
    (hf : IsMultiHomog f (blockDeg d.k₀ n)) (hf' : IsMultiHomog f' (blockDeg d.k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    pairValH d.A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') (fun p => c p.1 * z p) =
      pairValH d.A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') z := by
  simp only [pairValH, eval_map_int_rat]
  rw [SupBoundBlock.eval_torus_blockDeg hf, SupBoundBlock.eval_torus_blockDeg hf', d.A.smul c z hc, d.deg,
    prod_unitDeg]
  set u := c d.k₀ ^ n
  set w := eval z (map (Int.castRingHom ℂ) f)
  set w' := eval z (map (Int.castRingHom ℂ) f')
  have hu : u * starRingEnd ℂ u = ((‖c d.k₀‖ ^ (2 * n) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, mul_comm n 2]
  have hne : ((‖c d.k₀‖ ^ (2 * n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ (norm_ne_zero_iff.2 (hc d.k₀))
  calc u * w * starRingEnd ℂ (u * w') / (((‖c d.k₀‖ * d.A.h z) ^ (2 * n) : ℝ) : ℂ)
      = (u * starRingEnd ℂ u) * (w * starRingEnd ℂ w') /
          (((‖c d.k₀‖ ^ (2 * n) : ℝ) : ℂ) * ((d.A.h z ^ (2 * n) : ℝ) : ℂ)) := by
        rw [map_mul, mul_pow]
        push_cast
        ring
    _ = w * starRingEnd ℂ w' / ((d.A.h z ^ (2 * n) : ℝ) : ℂ) := by
        rw [hu]
        exact mul_div_mul_left _ _ hne

theorem pairValH_continuousOn (d : HSMBlockDatum D K ι Ω) (n : ℕ) (f f' : MRing ι) :
    ContinuousOn (pairValH d.A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f'))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have he : pairValH d.A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') = fun z =>
      eval z (map (Int.castRingHom ℂ) f) * starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f')) /
        ((d.A.h z ^ (2 * n) : ℝ) : ℂ) := by
    funext z
    simp only [pairValH, eval_map_int_rat]
  rw [he]
  refine ContinuousOn.div (((MvPolynomial.continuous_eval _).mul
    (Complex.continuous_conj.comp (MvPolynomial.continuous_eval _))).continuousOn)
    (Complex.continuous_ofReal.comp_continuousOn ((h_continuousOn d).pow _)) fun z hz => ?_
  exact Complex.ofReal_ne_zero.2 (pow_ne_zero _ (d.A.pos z hz).ne')

theorem blockGram_eq (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (k l : Fin r) :
    blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) k l =
      (1 / 2) * ((∫ x, pairRe d.A n (f k) (f l) (blockPt d x) ∂d.dV) +
        ∫ x, pairRe d.A n (f k) (f l) (conjPt (blockPt d x)) ∂d.dV) := by
  have hi := integrable_blockPt d (pairValH_continuousOn d n (f k) (f l))
    (pairValH_torus d (hf k) (hf l))
  have e1 := (integral_re hi.1).symm
  have e2 := (integral_re hi.2).symm
  simp only [RCLike.re_to_complex, pairValH_re] at e1 e2
  simp only [blockGram]
  rw [e1, e2]

theorem pairRe_integrable (d : HSMBlockDatum D K ι Ω) (n : ℕ) {f f' : MRing ι}
    (hf : IsMultiHomog f (blockDeg d.k₀ n)) (hf' : IsMultiHomog f' (blockDeg d.k₀ n)) :
    Integrable (fun x => pairRe d.A n f f' (blockPt d x)) d.dV ∧
      Integrable (fun x => pairRe d.A n f f' (conjPt (blockPt d x))) d.dV := by
  have hi := integrable_blockPt d (pairValH_continuousOn d n f f') (pairValH_torus d hf hf')
  simp only [← pairValH_re]
  exact ⟨hi.1.re, hi.2.re⟩

def comb {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℝ) (z : (Σ k, ι k) → ℂ) : ℂ :=
  ∑ k, (a k : ℂ) * eval z (map (Int.castRingHom ℂ) (f k))

theorem comb_re {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℝ) (z : (Σ k, ι k) → ℂ) :
    (comb f a z).re = ∑ k, a k * (eval z (map (Int.castRingHom ℂ) (f k))).re := by
  simp [comb, Complex.re_sum]

theorem comb_im {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℝ) (z : (Σ k, ι k) → ℂ) :
    (comb f a z).im = ∑ k, a k * (eval z (map (Int.castRingHom ℂ) (f k))).im := by
  simp [comb, Complex.im_sum]

theorem quad_pairRe (A : HermLine ι) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℝ)
    (z : (Σ k, ι k) → ℂ) :
    ∑ k, a k * ∑ l, pairRe A n (f k) (f l) z * a l = ‖comb f a z‖ ^ 2 / A.h z ^ (2 * n) := by
  rw [Complex.sq_norm, Complex.normSq_apply, comb_re, comb_im, Finset.sum_mul_sum, Finset.sum_mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [pairRe]
  ring

theorem sum_integral {X : Type*} [MeasurableSpace X] (μ : Measure X) {r : ℕ} (a b : Fin r → Fin r → ℝ)
    (g : Fin r → Fin r → X → ℝ) (hg : ∀ k l, Integrable (g k l) μ) :
    ∑ k, ∑ l, a k l * (∫ x, g k l x ∂μ) * b k l = ∫ x, ∑ k, ∑ l, a k l * g k l x * b k l ∂μ := by
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => ((hg k l).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ fun l _ => ((hg k l).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_mul_const, integral_const_mul]

theorem gram_quad (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) =
      (1 / 2) * ((∫ x, ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n) ∂d.dV) +
        ∫ x, ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n) ∂d.dV) := by
  simp only [dotProduct, Matrix.mulVec, blockGram_eq d n f hf]
  have h1 := sum_integral d.dV (fun k _ => a k) (fun _ l => a l)
    (fun k l x => pairRe d.A n (f k) (f l) (blockPt d x)) fun k l => (pairRe_integrable d n (hf k) (hf l)).1
  have h2 := sum_integral d.dV (fun k _ => a k) (fun _ l => a l)
    (fun k l x => pairRe d.A n (f k) (f l) (conjPt (blockPt d x)))
    fun k l => (pairRe_integrable d n (hf k) (hf l)).2
  simp only [← quad_pairRe, Finset.mul_sum, ← mul_assoc] at h1 h2 ⊢
  rw [← h1, ← h2, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isMultiHomog_zsum {r : ℕ} (f : Fin r → MRing ι) (m : Fin r → ℤ) {e : K → ℕ}
    (hf : ∀ k, IsMultiHomog (f k) e) : IsMultiHomog (∑ k, m k • f k) e := by
  classical
  intro μ hμ k
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hμ)
  exact hf j μ (MvPolynomial.support_smul hj) k

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_sub' {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem comb_int {r : ℕ} (f : Fin r → MRing ι) (m : Fin r → ℤ) (z : (Σ k, ι k) → ℂ) :
    comb f (fun k => (m k : ℝ)) z = eval z (map (Int.castRingHom ℂ) (∑ k, m k • f k)) := by
  simp [comb, map_sum, zsmul_eq_mul]

theorem blockL2Norm_sum_eq_sqrt_gram (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (m : Fin r → ℤ) :
    blockL2Norm d n (∑ k, m k • f k) = Real.sqrt ((fun k => (m k : ℝ)) ⬝ᵥ
      (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ))) := by
  rw [gram_quad d n f hf, blockL2Norm]
  simp only [comb_int, div_pow, ← pow_mul']

theorem blockL2Norm_le_one_of_sup_bound (d : HSMBlockDatum D K ι Ω) (n : ℕ) {F : MRing ι} (hF : IsMultiHomog F (blockDeg d.k₀ n))
    (h : ∀ z ∈ mcPts (mCoordIdeal d.y), ‖eval z (map (Int.castRingHom ℂ) F)‖ ≤ d.A.h z ^ n) :
    blockL2Norm d n F ≤ 1 := by
  have := d.vol.1
  have hi := integrable_blockPt d (Φ := fun z => (‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n) ^ 2)
    ((ratio_continuousOn d F n).pow 2) fun c z hc => by rw [ratio_torus d hF c z hc]
  have hle : ∀ z ∈ mcPts (mCoordIdeal d.y),
      (‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n) ^ 2 ≤ 1 := by
    intro z hz
    have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
    have h1 : ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ 1 := (div_le_one hp).2 (h z hz)
    have h0 : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n := by positivity
    nlinarith
  have h1 : ∫ x, (‖eval (blockPt d x) (map (Int.castRingHom ℂ) F)‖ / d.A.h (blockPt d x) ^ n) ^ 2 ∂d.dV ≤ 1 :=
    calc _ ≤ ∫ _, (1 : ℝ) ∂d.dV := integral_mono hi.1 (integrable_const _) fun x => hle _ (blockPt_mem d x)
      _ = 1 := by simp
  have h2 : ∫ x, (‖eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) F)‖ /
      d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV ≤ 1 :=
    calc _ ≤ ∫ _, (1 : ℝ) ∂d.dV := integral_mono hi.2 (integrable_const _)
          fun x => hle _ (conjPt_mem_mcPts (blockPt_mem d x))
      _ = 1 := by simp
  rw [blockL2Norm]
  calc Real.sqrt _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    _ = 1 := Real.sqrt_one

theorem isSmallH_iff (d : HSMBlockDatum D K ι Ω) (n : ℕ) {F : MRing ι} (hF : IsMultiHomog F (blockDeg d.k₀ n)) :
    IsSmallH (mCoordIdeal d.y) d.y d.A n (aeval d.y F) ↔
      ∀ z ∈ mcPts (mCoordIdeal d.y), ‖eval z (map (Int.castRingHom ℂ) F)‖ ≤ d.A.h z ^ n := by
  constructor
  · intro h z hz
    have := h (blockDeg d.k₀ n) 0 F 1 z hF isMultiHomog_one'
      (fun k => by by_cases hk : k = d.k₀ <;> simp [d.deg, blockDeg, unitDeg, hk]) (by simp) hz
    simpa using this
  · intro h dg dh g g' z hg hg' hdeg hval hz
    have hdg : dg = blockDeg d.k₀ n + dh := by
      funext k
      have := hdeg k
      rw [d.deg] at this
      by_cases hk : k = d.k₀
      · subst hk
        simp only [unitDeg, if_true, mul_one] at this
        simp only [Pi.add_apply, blockDeg, if_true]
        omega
      · simp only [unitDeg, hk, if_false, mul_zero, add_zero] at this
        simp only [Pi.add_apply, blockDeg, hk, if_false, zero_add]
        omega
    have hmh : IsMultiHomog (g - F * g') dg := isMultiHomog_sub' hg (hdg ▸ isMultiHomog_mul' hF hg')
    have hy : aeval d.y (g - F * g') = 0 := by rw [map_sub, map_mul, hval, sub_self]
    have hmem : g - F * g' ∈ mCoordIdeal d.y := by
      show mConeMap d.y _ = 0
      rw [ProjLine.mConeMap_eq_of_isMultiHomog d.y hmh, hy, map_zero, zero_mul]
    have h0 := hz.2 _ hmem
    rw [map_sub, map_mul, eval_sub, eval_mul, sub_eq_zero] at h0
    rw [h0, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg _)

end SupBoundCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
