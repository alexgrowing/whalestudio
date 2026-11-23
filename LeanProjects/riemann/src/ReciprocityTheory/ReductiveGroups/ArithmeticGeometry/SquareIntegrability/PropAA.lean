import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CardSupportLeAndSumTwoPowLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IntegrableNormPowMulExpNegMulNormSq

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def paW (q : ℕ) (v : EuclideanSpace ℂ ι) : ℝ := Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)

def paIP (q : ℕ) (F G : EuclideanSpace ℂ ι → ℂ) : ℂ :=
  ∫ v, F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ)

def paN (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : ℝ := Real.sqrt (paIP q F F).re

def paPF (p : MvPolynomial ι ℂ) : EuclideanSpace ℂ ι → ℂ := fun v => MvPolynomial.eval (fun i => v i) p

def paMono (α : ι →₀ ℕ) : EuclideanSpace ℂ ι → ℂ := paPF (MvPolynomial.monomial α 1)

def paS (c : ℕ) : Finset (ι →₀ ℕ) :=
  ((Fintype.piFinset fun _ : ι => Finset.range (c + 1)).map
    (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).symm.toEmbedding).filter (fun α => α.degree ≤ c)

def paPoly (c : ℕ) : Submodule ℂ (EuclideanSpace ℂ ι → ℂ) :=
  Submodule.span ℂ (paMono '' ((paS (ι := ι) c : Finset (ι →₀ ℕ)) : Set (ι →₀ ℕ)))

def paU (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun v => cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)

def paD (α : ι →₀ ℕ) (H : EuclideanSpace ℂ ι → ℂ) : ℂ :=
  polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) H 0

def paFact (α : ι →₀ ℕ) : ℕ := ∏ i, (α i).factorial

def paJet (c : ℕ) (H : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  ∑ α ∈ paS c, (paD α H / paFact α) • paMono α

theorem mem_paS {c : ℕ} {α : ι →₀ ℕ} : α ∈ paS c ↔ α.degree ≤ c := by
  simp only [paS, Finset.mem_filter, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨⟨α, fun i => ?_, by simp⟩, h⟩
    have := Finsupp.le_degree i α
    omega

theorem paS_deg {c : ℕ} {α : ι →₀ ℕ} (h : α ∈ paS c) : α.degree ≤ c := mem_paS.1 h

theorem sum_eq_degree (s : ι →₀ ℕ) : (s.sum fun _ e => e) = s.degree := by
  rw [Finsupp.degree_apply]; rfl

theorem paPF_eq_sum (p : MvPolynomial ι ℂ) :
    paPF p = ∑ m ∈ p.support, p.coeff m • paMono m := by
  funext v
  conv_lhs => rw [paPF, p.as_sum, map_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, paMono, paPF, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun m _ => by ring

theorem paMono_mem {c : ℕ} {α : ι →₀ ℕ} (h : α ∈ paS c) : paMono α ∈ paPoly c :=
  Submodule.subset_span ⟨α, h, rfl⟩

theorem paPF_mem_paPoly {c : ℕ} {p : MvPolynomial ι ℂ} (hp : p.totalDegree ≤ c) :
    paPF p ∈ paPoly c := by
  rw [paPF_eq_sum]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (paMono_mem (mem_paS.2 ?_))
  have := MvPolynomial.le_totalDegree hm
  rw [sum_eq_degree] at this
  omega

theorem paPF_add (p r : MvPolynomial ι ℂ) : paPF (p + r) = paPF p + paPF r := by
  funext v; simp [paPF]

theorem paPF_smul (a : ℂ) (p : MvPolynomial ι ℂ) : paPF (MvPolynomial.C a * p) = a • paPF p := by
  funext v; simp [paPF]

theorem paPoly_exists {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ p : MvPolynomial ι ℂ, p.totalDegree ≤ c ∧ F = paPF p := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    refine ⟨MvPolynomial.monomial α 1, ?_, rfl⟩
    calc (MvPolynomial.monomial α (1 : ℂ)).totalDegree ≤ α.sum (fun _ => id) :=
          MvPolynomial.totalDegree_monomial_le _ _
      _ = α.degree := sum_eq_degree α
      _ ≤ c := paS_deg hα
  | zero => exact ⟨0, by simp, by funext v; simp [paPF]⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨r, hr, rfl⟩ := hy
    exact ⟨p + r, (MvPolynomial.totalDegree_add _ _).trans (max_le hp hr), (paPF_add p r).symm⟩
  | smul a x _ hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨MvPolynomial.C a * p, ?_, (paPF_smul a p).symm⟩
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simpa using hp

theorem paJet_mem (c : ℕ) (H : EuclideanSpace ℂ ι → ℂ) : paJet c H ∈ paPoly c :=
  Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ (paMono_mem hα)

theorem paPoly_fd (c : ℕ) : FiniteDimensional ℂ (paPoly (ι := ι) c) :=
  FiniteDimensional.span_of_finite ℂ ((paS c).finite_toSet.image _)

theorem paPF_continuous (p : MvPolynomial ι ℂ) : Continuous (paPF p) := by
  unfold paPF
  exact (MvPolynomial.continuous_eval p).comp (by fun_prop)

theorem paPoly_continuous {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) : Continuous F := by
  obtain ⟨p, -, rfl⟩ := paPoly_exists hF
  exact paPF_continuous p

theorem paMono_norm_le (α : ι →₀ ℕ) (v : EuclideanSpace ℂ ι) : ‖paMono α v‖ ≤ ‖v‖ ^ α.degree := by
  simp only [paMono, paPF, MvPolynomial.eval_monomial, one_mul, Finsupp.prod, norm_prod, norm_pow]
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun i _ => by positivity)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le v i) _)

theorem paPoly_growth {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖F v‖ ≤ C * (1 + ‖v‖) ^ c := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    refine ⟨1, zero_le_one, fun v => ?_⟩
    rw [one_mul]
    refine (paMono_norm_le α v).trans ?_
    calc ‖v‖ ^ α.degree ≤ (1 + ‖v‖) ^ α.degree := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
      _ ≤ (1 + ‖v‖) ^ c := pow_le_pow_right₀ (by linarith [norm_nonneg v]) (paS_deg hα)
  | zero => exact ⟨0, le_rfl, fun v => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C1, h1, hC1⟩ := hx
    obtain ⟨C2, h2, hC2⟩ := hy
    exact ⟨C1 + C2, by positivity, fun v => (norm_add_le _ _).trans (by
      have := hC1 v; have := hC2 v; nlinarith)⟩
  | smul a x _ hx =>
    obtain ⟨C, h, hC⟩ := hx
    refine ⟨‖a‖ * C, by positivity, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC v) (norm_nonneg _)

theorem paW_pos (q : ℕ) (v : EuclideanSpace ℂ ι) : 0 < paW q v := Real.exp_pos _

theorem paW_continuous (q : ℕ) : Continuous (paW (ι := ι) q) := by
  unfold paW; fun_prop

theorem pa_gauss_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : EuclideanSpace ℂ ι => Real.exp (-b * ‖v‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℂ ι) (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem pa_one_add_pow_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + t ^ n) := by
        have : 0 ≤ t ^ n := pow_nonneg ht n
        nlinarith [pow_pos (two_pos (α := ℝ)) n]
  · calc (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * t ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + t ^ n) := by nlinarith [pow_pos (two_pos (α := ℝ)) n]

theorem pa_pow_gauss_le (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    (1 + t) ^ n * Real.exp (-b * t ^ 2) ≤
      2 ^ n * (2 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
  have h1 := pow_mul_exp_neg_mul_sq_le n hb ht
  have h2 : Real.exp (-b * t ^ 2) ≤ Real.exp (-(b / 2) * t ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  have h3 := pa_one_add_pow_le n ht
  have hE : 0 ≤ Real.exp (-b * t ^ 2) := (Real.exp_pos _).le
  calc (1 + t) ^ n * Real.exp (-b * t ^ 2) ≤ 2 ^ n * (1 + t ^ n) * Real.exp (-b * t ^ 2) :=
        mul_le_mul_of_nonneg_right h3 hE
    _ = 2 ^ n * (Real.exp (-b * t ^ 2) + t ^ n * Real.exp (-b * t ^ 2)) := by ring
    _ ≤ 2 ^ n * (Real.exp (-(b / 2) * t ^ 2) + (1 + n.factorial * (2 / b) ^ n) *
        Real.exp (-(b / 2) * t ^ 2)) := by gcongr
    _ = _ := by ring

theorem pa_integrable_of_le {E' : Type*} [NormedAddCommGroup E'] {f : EuclideanSpace ℂ ι → E'}
    (hf : Continuous f) (n : ℕ) {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (h : ∀ v, ‖f v‖ ≤ C * ((1 + ‖v‖) ^ n * Real.exp (-b * ‖v‖ ^ 2))) : Integrable f := by
  refine ((pa_gauss_integrable (ι := ι) (half_pos hb)).const_mul
    (C * (2 ^ n * (2 + n.factorial * (2 / b) ^ n)))).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  refine (h v).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (pa_pow_gauss_le n hb (norm_nonneg v)) hC

theorem pa_bound2 {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖F v‖ * ‖G v‖ * paW q v ≤
      C * ((1 + ‖v‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)) := by
  obtain ⟨C1, h1, hC1⟩ := paPoly_growth hF
  obtain ⟨C2, h2, hC2⟩ := paPoly_growth hG
  refine ⟨C1 * C2, by positivity, fun v => ?_⟩
  have hw := (paW_pos q v).le
  have e : (1 + ‖v‖) ^ (2 * c) = (1 + ‖v‖) ^ c * (1 + ‖v‖) ^ c := by rw [two_mul, pow_add]
  rw [e, paW]
  have := mul_le_mul (hC1 v) (hC2 v) (norm_nonneg _) (by positivity)
  have hw' := Real.exp_pos (-(q * Real.pi) * ‖v‖ ^ 2)
  nlinarith

theorem gaussianInner_integrable {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) :
    Integrable (fun v => F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ)) := by
  obtain ⟨C, hC, h⟩ := pa_bound2 hq hF hG
  have hb : 0 < (q : ℝ) * Real.pi := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    positivity
  refine pa_integrable_of_le (by
    have := paPoly_continuous hF; have := paPoly_continuous hG; have := paW_continuous (ι := ι) q
    fun_prop) (2 * c) hb hC (fun v => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (paW_pos q v).le]
  simpa [neg_mul] using h v

theorem gaussianInner_integrable_norm {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : Integrable (fun v => ‖F v‖ * ‖G v‖ * paW q v) := by
  have := (gaussianInner_integrable hq hF hG).norm
  refine this.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (paW_pos q v).le]

theorem gaussianInner_add_left {q c : ℕ} (hq : 1 ≤ q) {F G H : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) (hH : H ∈ paPoly c) : paIP q (F + G) H = paIP q F H + paIP q G H := by
  unfold paIP
  rw [← integral_add (gaussianInner_integrable hq hF hH) (gaussianInner_integrable hq hG hH)]
  congr 1; funext v; simp only [Pi.add_apply]; ring

theorem gaussianInner_smul_left (q : ℕ) (a : ℂ) (F G : EuclideanSpace ℂ ι → ℂ) :
    paIP q (a • F) G = a * paIP q F G := by
  unfold paIP
  rw [← integral_const_mul]
  congr 1; funext v; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem gaussianInner_conj_symm (q : ℕ) (F G : EuclideanSpace ℂ ι → ℂ) :
    paIP q G F = (starRingEnd ℂ) (paIP q F G) := by
  unfold paIP
  rw [← integral_conj]
  congr 1; funext v
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem gaussianInner_self (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    paIP q F F = ((∫ v, ‖F v‖ ^ 2 * paW q v : ℝ) : ℂ) := by
  unfold paIP
  rw [← integral_complex_ofReal]
  congr 1; funext v
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

theorem gaussianInner_self_re (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    paIP q F F = ((paIP q F F).re : ℂ) ∧ 0 ≤ (paIP q F F).re := by
  rw [gaussianInner_self, Complex.ofReal_re]
  exact ⟨rfl, integral_nonneg fun v => by have := paW_pos q v; positivity⟩

theorem pa_cs_real {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → 2 * t * X ≤ t ^ 2 * A + B) : X ≤ Real.sqrt A * Real.sqrt B := by
  rw [← Real.sqrt_mul hA]
  rcases hX.lt_or_eq with hX | hX
  · rcases hA.lt_or_eq with hA' | hA'
    · have := h (X / A) (div_pos hX hA')
      have e : (X / A) ^ 2 * A = X * (X / A) := by field_simp
      rw [e] at this
      have h2 : X * X ≤ A * B := by
        have : X * (X / A) ≤ B := by nlinarith
        rw [mul_div_assoc', div_le_iff₀ hA'] at this
        linarith
      exact Real.le_sqrt_of_sq_le (by nlinarith)
    · exfalso
      have := h ((B + 1) / X) (by positivity)
      rw [← hA'] at this
      have e : 2 * ((B + 1) / X) * X = 2 * (B + 1) := by field_simp
      rw [e] at this
      linarith
  · rw [← hX]; exact Real.sqrt_nonneg _

theorem norm_gaussianInner_le {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : ‖paIP q F G‖ ≤ paN q F * paN q G := by
  have hA : (paIP q F F).re = ∫ v, ‖F v‖ * ‖F v‖ * paW q v := by
    rw [gaussianInner_self, Complex.ofReal_re]; congr 1; funext v; ring
  have hB : (paIP q G G).re = ∫ v, ‖G v‖ * ‖G v‖ * paW q v := by
    rw [gaussianInner_self, Complex.ofReal_re]; congr 1; funext v; ring
  have h1 : ‖paIP q F G‖ ≤ ∫ v, ‖F v‖ * ‖G v‖ * paW q v := by
    unfold paIP
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext v
    simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (paW_pos q v).le]
  refine h1.trans ?_
  unfold paN
  rw [hA, hB]
  refine pa_cs_real (integral_nonneg fun v => by have := paW_pos q v; positivity)
    (integral_nonneg fun v => by have := paW_pos q v; positivity)
    (integral_nonneg fun v => by have := paW_pos q v; positivity) fun t ht => ?_
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((gaussianInner_integrable_norm hq hF hF).const_mul _) (gaussianInner_integrable_norm hq hG hG)]
  refine integral_mono ((gaussianInner_integrable_norm hq hF hG).const_mul _)
    (((gaussianInner_integrable_norm hq hF hF).const_mul _).add (gaussianInner_integrable_norm hq hG hG)) fun v => ?_
  have := (paW_pos q v).le
  have h2 : 0 ≤ (t * ‖F v‖ - ‖G v‖) ^ 2 * paW q v := by positivity
  simp only
  nlinarith

theorem paN_eq_zero {q c : ℕ} (hq : 1 ≤ q) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (h0 : paN q F = 0) : F = 0 := by
  obtain ⟨-, hre⟩ := gaussianInner_self_re q F
  have hz : (paIP q F F).re = 0 := by
    unfold paN at h0
    have := Real.sqrt_eq_zero'.mp h0
    linarith
  rw [gaussianInner_self, Complex.ofReal_re] at hz
  have hi : Integrable (fun v => ‖F v‖ ^ 2 * paW q v) := by
    have := gaussianInner_integrable_norm hq hF hF
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only; ring
  have hc : Continuous (fun v => ‖F v‖ ^ 2 * paW q v) := by
    have := paPoly_continuous hF; have := paW_continuous (ι := ι) q; fun_prop
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => by have := paW_pos q v; positivity) hi).1 hz
  have heq := (Continuous.ae_eq_iff_eq volume hc continuous_const).1 hae
  funext v
  have := congrFun heq v
  simp only [Pi.zero_apply] at this ⊢
  have hw := paW_pos q v
  have : ‖F v‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this)

theorem pa_tm_inj {a b : ι →₀ ℕ} (h : Finsupp.toMultiset a = Finsupp.toMultiset b) : a = b := by
  rw [← Finsupp.toMultiset_toFinsupp a, h, Finsupp.toMultiset_toFinsupp]

def paPD : (n : ℕ) → (Fin n → ι) → MvPolynomial ι ℂ → MvPolynomial ι ℂ
  | 0, _, p => p
  | n + 1, m, p => paPD n (Fin.init m) (MvPolynomial.pderiv (m (Fin.last n)) p)

theorem paPF_X_mul (p : MvPolynomial ι ℂ) (j : ι) :
    paPF (p * MvPolynomial.X j) = paPF p * fun v : EuclideanSpace ℂ ι => v j := by
  funext v; simp [paPF]

theorem paPF_diff (p : MvPolynomial ι ℂ) : Differentiable ℂ (paPF p) ∧
    ∀ (j : ι) (y : EuclideanSpace ℂ ι),
      fderiv ℂ (paPF p) y (EuclideanSpace.single j 1) = paPF (MvPolynomial.pderiv j p) y := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : paPF (MvPolynomial.C a) = fun _ : EuclideanSpace ℂ ι => a := by funext v; simp [paPF]
    rw [e]
    refine ⟨differentiable_const a, fun j y => ?_⟩
    simp [paPF]
  | add p r hp hr =>
    rw [paPF_add]
    refine ⟨hp.1.add hr.1, fun j y => ?_⟩
    rw [fderiv_add (hp.1 y) (hr.1 y), ContinuousLinearMap.add_apply, hp.2, hr.2, map_add, paPF_add]
    rfl
  | mul_X p k hp =>
    have hd : Differentiable ℂ (fun v : EuclideanSpace ℂ ι => v k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).differentiable
    rw [paPF_X_mul]
    refine ⟨hp.1.mul hd, fun j y => ?_⟩
    rw [fderiv_mul (hp.1 y) (hd y)]
    have e1 : fderiv ℂ (fun v : EuclideanSpace ℂ ι => v k) y =
        (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ) :=
      (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).fderiv
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      e1, hp.2, Derivation.leibniz, MvPolynomial.pderiv_X]
    simp only [EuclideanSpace.coe_proj, EuclideanSpace.single_apply, smul_eq_mul, paPF, map_add,
      map_mul, MvPolynomial.eval_X, Pi.single_apply]
    by_cases h : j = k
    · subst h; simp <;> ring
    · simp [h, Ne.symm h] <;> ring

theorem paPF_contDiff (p : MvPolynomial ι ℂ) : ContDiff ℂ (⊤ : ℕ∞) (paPF p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : paPF (MvPolynomial.C a) = fun _ : EuclideanSpace ℂ ι => a := by funext v; simp [paPF]
    rw [e]; exact contDiff_const
  | add p r hp hr => rw [paPF_add]; exact hp.add hr
  | mul_X p k hp =>
    rw [paPF_X_mul]
    exact hp.mul (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff

theorem paPF_iter (n : ℕ) : ∀ (p : MvPolynomial ι ℂ) (m : Fin n → ι) (x : EuclideanSpace ℂ ι),
    iteratedFDeriv ℂ n (paPF p) x (fun k => EuclideanSpace.single (m k) 1) = paPF (paPD n m p) x := by
  induction n with
  | zero => intro p m x; simp [paPD]
  | succ n ih =>
    intro p m x
    rw [iteratedFDeriv_succ_apply_right]
    have hc : ContDiff ℂ (⊤ : ℕ∞) (fderiv ℂ (paPF p)) :=
      (paPF_contDiff p).fderiv_right (by simp)
    rw [← iteratedFDeriv_clm_apply_const_apply hc (by exact_mod_cast le_top)]
    have e : (fun y => fderiv ℂ (paPF p) y (EuclideanSpace.single (m (Fin.last n)) 1)) =
        paPF (MvPolynomial.pderiv (m (Fin.last n)) p) := by
      funext y; exact (paPF_diff p).2 _ y
    rw [e]
    exact ih _ (Fin.init m) x

theorem paFact_succ (β : ι →₀ ℕ) (i : ι) (h : 1 ≤ β i) :
    (paFact β : ℂ) = (β i : ℂ) * paFact (β - Finsupp.single i 1) := by
  unfold paFact
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have e : ∏ x ∈ Finset.univ.erase i, (β x).factorial =
      ∏ x ∈ Finset.univ.erase i, ((β - Finsupp.single i 1 : ι →₀ ℕ) x).factorial := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hx).symm, Nat.sub_zero]
  rw [e, Finsupp.tsub_apply, Finsupp.single_eq_same]
  obtain ⟨k, hk⟩ : ∃ k, β i = k + 1 := ⟨β i - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast; ring

theorem paPD_monomial (n : ℕ) : ∀ (m : Fin n → ι) (β : ι →₀ ℕ) (a : ℂ),
    MvPolynomial.constantCoeff (paPD n m (MvPolynomial.monomial β a)) =
      if Finsupp.toMultiset β = (List.ofFn m : Multiset ι) then a * paFact β else 0 := by
  induction n with
  | zero =>
    intro m β a
    simp only [paPD, MvPolynomial.constantCoeff_monomial, List.ofFn_zero, Multiset.coe_nil]
    by_cases h : β = 0
    · subst h; simp [paFact]
    · rw [if_neg h, if_neg]
      intro h2; exact h (pa_tm_inj (by rw [h2, Finsupp.toMultiset_zero]))
  | succ n ih =>
    intro m β a
    simp only [paPD, MvPolynomial.pderiv_monomial]
    rw [ih]
    set i := m (Fin.last n)
    have hl : ((List.ofFn m : List ι) : Multiset ι) = (List.ofFn (Fin.init m) : Multiset ι) + {i} := by
      rw [List.ofFn_succ', List.concat_eq_append, ← Multiset.coe_add]
      rfl
    rw [hl]
    by_cases hb : β i = 0
    · rw [hb]
      simp only [Nat.cast_zero, mul_zero, zero_mul, ite_self]
      rw [if_neg]
      intro h
      have := congrArg (Multiset.count i) h
      rw [Finsupp.count_toMultiset, hb, Multiset.count_add, Multiset.count_singleton_self] at this
      omega
    · have hb1 : 1 ≤ β i := Nat.one_le_iff_ne_zero.mpr hb
      have hle : Finsupp.single i 1 ≤ β := Finsupp.single_le_iff.mpr hb1
      have hsplit : Finsupp.toMultiset β = Finsupp.toMultiset (β - Finsupp.single i 1) + {i} := by
        conv_lhs => rw [← tsub_add_cancel_of_le hle]
        rw [map_add, Finsupp.toMultiset_single, one_nsmul]
      rw [hsplit]
      by_cases hc : Finsupp.toMultiset (β - Finsupp.single i 1) = (List.ofFn (Fin.init m) : Multiset ι)
      · rw [if_pos hc, if_pos (by rw [hc]), paFact_succ β i hb1]; ring
      · rw [if_neg hc, if_neg (fun h => hc (add_right_cancel h))]

theorem paPF_zero (p : MvPolynomial ι ℂ) : paPF p 0 = MvPolynomial.constantCoeff p := by
  have : (fun i => (0 : EuclideanSpace ℂ ι) i) = 0 := by funext i; simp
  show MvPolynomial.eval (fun i => (0 : EuclideanSpace ℂ ι) i) p = _
  rw [this, MvPolynomial.eval_zero]

theorem paD_mono (α β : ι →₀ ℕ) : paD α (paMono β) = if α = β then (paFact α : ℂ) else 0 := by
  unfold paD polyDeriv
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
  have := paPF_iter _ (MvPolynomial.monomial β 1)
    (fun k => (Finsupp.toMultiset α).toList.get (k.cast (Multiset.length_toList _).symm)) 0
  simp only at this ⊢
  rw [paMono, this, paPF_zero, paPD_monomial]
  have hl : List.ofFn (fun k : Fin (Multiset.card (Finsupp.toMultiset α)) =>
      (Finsupp.toMultiset α).toList.get (k.cast (Multiset.length_toList _).symm)) =
      (Finsupp.toMultiset α).toList := by
    apply List.ext_get (by simp)
    intro k h1 h2; simp
  rw [hl, Multiset.coe_toList]
  by_cases h : α = β
  · subst h; simp
  · rw [if_neg (fun h' => h (pa_tm_inj h').symm), if_neg h]

end

end ReciprocityTheory.ChartRestriction.G.I2
