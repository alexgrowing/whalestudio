import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AreaBoundedOfDiscrEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators UpperHalfPlane Real Pointwise
open MeasureTheory

noncomputable section

namespace GlobalTheory.OddThetaNorm

theorem setAverage_eq_of_fundamental {Λ : AddSubgroup ℂ} [Countable Λ] {s t : Set ℂ}
    (hs : IsAddFundamentalDomain Λ s volume) (ht : IsAddFundamentalDomain Λ t volume)
    {f : ℂ → ℝ} (hf : ∀ ω ∈ Λ, ∀ z, f (z + ω) = f z) : ⨍ z in s, f z = ⨍ z in t, f z := by
  rw [setAverage_eq, setAverage_eq, Measure.real, Measure.real, hs.measure_eq ht,
    hs.setIntegral_eq ht fun g x => by
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm, hf _ g.2]]

theorem setAverage_add {Λ : AddSubgroup ℂ} [Countable Λ] {s : Set ℂ}
    (hs : IsAddFundamentalDomain Λ s volume)
    {f : ℂ → ℝ} (hf : ∀ ω ∈ Λ, ∀ z, f (z + ω) = f z) (t : ℂ) :
    ⨍ z in s, f (z + t) = ⨍ z in s, f z := by
  rw [setAverage_eq_of_fundamental hs (hs.vadd_of_comm t) hf, setAverage_eq, setAverage_eq,
    Measure.real, Measure.real, measure_vadd]
  congr 1
  have := (measurePreserving_add_left volume t).setIntegral_image_emb
    (measurableEmbedding_addLeft t) f s
  simp only [add_comm _ t]
  exact this.symm

theorem setAverage_fundamentalDomain {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ ℂ) (f : ℂ → ℝ) :
    ⨍ z in ZSpan.fundamentalDomain b, f z =
      ∫ p in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1), f (∑ i, p i • b i) := by
  let e : (ι → ℝ) ≃L[ℝ] ℂ := b.equivFun.symm.toContinuousLinearEquiv
  have he : ∀ p, e p = ∑ i, p i • b i := fun p => b.equivFun_symm_apply p
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hpre : e ⁻¹' ZSpan.fundamentalDomain b = Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1) := by
    ext p
    have : ∀ i, b.repr (e p) i = p i := fun i => congrFun (b.equivFun.apply_symm_apply p) i
    simp [ZSpan.mem_fundamentalDomain, this]
  set μ : Measure ℂ := Measure.map e volume with hμ
  have hv := Measure.isAddLeftInvariant_eq_smul (volume : Measure ℂ) μ
  have hc := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure ℂ) μ).ne'
  set c := Measure.addHaarScalarFactor (volume : Measure ℂ) μ
  have h1 : μ (ZSpan.fundamentalDomain b) = 1 := by
    rw [hμ, hme.map_apply, hpre, volume_pi_pi]
    simp
  rw [setAverage_eq, hv, Measure.restrict_smul, integral_smul_nnreal_measure, Measure.real,
    Measure.smul_apply, h1, hμ, hme.setIntegral_map, hpre]
  simp only [he]
  have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  simp [NNReal.smul_def, this]

theorem jacobiTheta₂_add_lattice (z τ : ℂ) (m k : ℤ) :
    jacobiTheta₂ (z + (m * τ + k)) τ =
      Complex.exp (-π * Complex.I * (m ^ 2 * τ + 2 * m * z)) * jacobiTheta₂ z τ := by
  rw [jacobiTheta₂, jacobiTheta₂, ← (Equiv.addRight m).tsum_eq (fun n => jacobiTheta₂_term n z τ),
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨n * k, ?_⟩
  simp only [Equiv.coe_addRight]
  push_cast
  ring

theorem thetaTranslation_weighted_normSq_mul (Λ : AddSubgroup ℂ) (t : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    ‖U1 Λ t g z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ) =
      ‖g (z + t)‖ ^ 2 * Real.exp (-π * ‖z + t‖ ^ 2 / area Λ) := by
  rw [U1, norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  rw [show (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) by push_cast; rfl, Complex.sub_re,
    Complex.div_ofReal_re, Complex.div_ofReal_re]
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

def oddTheta (τ u : ℂ) : ℂ :=
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (g := 1) !![τ] ![1 / 2] ![1 / 2] ![u]

theorem differentiable_oddTheta (τ : ℍ) : Differentiable ℂ (oddTheta τ) := by
  have : oddTheta τ = fun z => Complex.exp (π * Complex.I * (τ / 4 + z + 1 / 2)) *
      jacobiTheta₂ (z + (τ + 1) / 2) τ := funext fun z => JacobiDeriv.thetaChar_half_half τ z
  rw [this]
  refine Differentiable.mul (by fun_prop) fun z => ?_
  exact ((hasDerivAt_jacobiTheta₂_fst (z + (τ + 1) / 2) τ.im_pos).comp_add_const z _).differentiableAt

theorem oddTheta_zero (τ : ℂ) : oddTheta τ 0 = 0 := by
  rw [oddTheta, JacobiDeriv.thetaChar_half_half, zero_add, JacobiDeriv.jacobiTheta₂_half_period,
    mul_zero]

theorem oddTheta_add_lattice (u τ : ℂ) (m k : ℤ) :
    oddTheta τ (u + (m * τ + k)) =
      Complex.exp (π * Complex.I * (k - m - m ^ 2 * τ - 2 * m * u)) * oddTheta τ u := by
  rw [oddTheta, oddTheta, JacobiDeriv.thetaChar_half_half, JacobiDeriv.thetaChar_half_half,
    add_right_comm u, jacobiTheta₂_add_lattice, ← mul_assoc, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  ring

def canTheta (a : ℂ) (τ : ℍ) (z : ℂ) : ℂ :=
  Complex.exp (π * (z / a) ^ 2 / (2 * τ.im)) * oddTheta τ (z / a)

theorem differentiable_canTheta (a : ℂ) (τ : ℍ) : Differentiable ℂ (canTheta a τ) := by
  have := differentiable_oddTheta τ
  unfold canTheta
  fun_prop

theorem deriv_canTheta (a : ℂ) (τ : ℍ) : deriv (canTheta a τ) 0 = deriv (oddTheta τ) 0 / a := by
  have h1 : HasDerivAt (fun z => oddTheta τ (z / a)) (deriv (oddTheta τ) 0 / a) 0 := by
    have := (differentiable_oddTheta τ (0 / a)).hasDerivAt.comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).div_const a)
    rw [zero_div, mul_one_div] at this
    exact this
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (π * (z / a) ^ 2 / (2 * τ.im))) 0 := by
    fun_prop
  have h3 := (h2.hasDerivAt.mul h1).deriv
  simp only [zero_div, oddTheta_zero, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Complex.exp_zero, one_mul] at h3
  exact h3

theorem exp_pi_I_int (j : ℤ) : Complex.exp (π * Complex.I * j) = if Even j then 1 else -1 := by
  rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h).neg_one_zpow

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

theorem half_mem_iff (m k : ℤ) : a * (m * (τ : ℂ) + k) / 2 ∈ Λ ↔ Even (k - m + m * k) := by
  have : Even (k - m + m * k) ↔ Even m ∧ Even k := by
    simp only [parity_simps]; tauto
  rw [this, h]
  constructor
  · rintro ⟨p, q, e⟩
    have e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ) := by
      refine mul_left_cancel₀ ha ?_
      push_cast
      linear_combination -2 * e
    have h1 := congrArg Complex.im e1
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1
    rw [h1, add_right_inj, Int.cast_inj] at e1
    exact ⟨⟨p, h1⟩, ⟨q, e1⟩⟩
  · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
    exact ⟨p, q, by push_cast; ring⟩

theorem thetaTranslation_canonicalOddTheta_lattice : ∀ ω ∈ Λ, ∀ z,
    U1 Λ ω (canTheta a τ) z = (if ω / 2 ∈ Λ then 1 else -1) * canTheta a τ z := by
  intro ω hω z
  obtain ⟨m, k, rfl⟩ := (h ω).1 hω
  simp only [half_mem_iff ha h]
  rw [← exp_pi_I_int, U1, canTheta, canTheta, LatticeAreaBound.area_eq ha h,
    show (z + a * (m * (τ : ℂ) + k)) / a = z / a + (m * (τ : ℂ) + k) by field_simp,
    oddTheta_add_lattice, ← mul_assoc (Complex.exp _), mul_right_comm, ← Complex.exp_add,
    ← Complex.exp_add, ← mul_assoc (Complex.exp _), ← Complex.exp_add]
  congr 2
  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  have hc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * τ.im * Complex.I := by
    apply Complex.ext <;> simp
    ring
  have ha' : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
  have hn : ((‖a‖ ^ 2 * τ.im : ℝ) : ℂ) = a * (starRingEnd ℂ) a * τ.im := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [hn]
  simp only [map_mul, map_add, map_intCast, hc]
  push_cast
  field_simp
  ring

theorem countable_lattice : Countable Λ := by
  refine Function.Surjective.countable
    (f := fun p : ℤ × ℤ => (⟨a * (p.1 * (τ : ℂ) + p.2), (h _).2 ⟨_, _, rfl⟩⟩ : Λ)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨m, n, rfl⟩ := (h x).1 hx
  exact ⟨(m, n), rfl⟩

theorem exists_basis : ∃ b : Module.Basis (Fin 1 ⊕ Fin 1) ℝ ℂ,
    (∀ i, b (.inl i) = a) ∧ (∀ i, b (.inr i) = a * τ) ∧
      IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain b) volume := by
  have hli : LinearIndependent ℝ (Sum.elim (fun _ => a) (fun _ => a * τ) : Fin 1 ⊕ Fin 1 → ℂ) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr,
      Complex.real_smul] at hg
    have e : (g (.inl 0) : ℂ) + g (.inr 0) * τ = 0 :=
      mul_left_cancel₀ ha (by linear_combination hg)
    have h1 := congrArg Complex.im e
    simp [τ.im_ne_zero] at h1
    simp [h1] at e
    rintro (i | i) <;> rwa [Subsingleton.elim i 0]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = Sum.elim (fun _ => a) (fun _ => a * τ) :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  refine ⟨b, fun i => by simp [hb], fun i => by simp [hb], ?_⟩
  have : Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    ext x
    rw [h, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun, hb]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr, zsmul_eq_mul]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨Sum.elim (fun _ => n) (fun _ => m), by simp; ring⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c (.inr 0), c (.inl 0), by ring⟩
  rw [this]
  exact ZSpan.isAddFundamentalDomain' b volume

theorem epsilon_fundamental : IsAddFundamentalDomain Λ
    (Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) volume := by
  obtain ⟨b, -, -, hb⟩ := exists_basis ha h
  exact Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) ⟨_, hb⟩

omit ha h in
theorem weight_invariant {g : ℂ → ℂ}
    (hg : ∀ ω ∈ Λ, ∀ z, U1 Λ ω g z = (if ω / 2 ∈ Λ then 1 else -1) * g z) :
    ∀ ω ∈ Λ, ∀ z, ‖g (z + ω)‖ ^ 2 * Real.exp (-π * ‖z + ω‖ ^ 2 / area Λ) =
      ‖g z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ) := by
  intro ω hω z
  rw [← thetaTranslation_weighted_normSq_mul, hg ω hω, norm_mul]
  split_ifs <;> simp

omit ha h in
theorem odd_theta_norm_smul (c : ℂ) (g : ℂ → ℂ) :
    nrm1Sq Λ (fun z => c * g z) = ‖c‖ ^ 2 * nrm1Sq Λ g := by
  simp only [nrm1Sq, norm_mul, mul_pow, mul_assoc, setAverage_eq, integral_const_mul, smul_eq_mul]
  ring

theorem odd_theta_norm_translate {g : ℂ → ℂ}
    (hg : ∀ ω ∈ Λ, ∀ z, U1 Λ ω g z = (if ω / 2 ∈ Λ then 1 else -1) * g z) (t : ℂ) :
    nrm1Sq Λ (U1 Λ t g) = nrm1Sq Λ g := by
  haveI := countable_lattice ha h
  simp only [nrm1Sq, thetaTranslation_weighted_normSq_mul]
  exact setAverage_add (epsilon_fundamental ha h)
    (f := fun z => ‖g z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ)) (weight_invariant hg) t

theorem odd_theta_norm_canonical : nrm1Sq Λ (canTheta a τ) = (Real.sqrt (2 * τ.im))⁻¹ := by
  haveI := countable_lattice ha h
  obtain ⟨b, h1, h2, hb⟩ := exists_basis ha h
  have key := ThetaNorm.integral_norm_sq_thetaChar 1 !![(τ : ℂ)] ![1 / 2] ![1 / 2]
    (by ext i j; fin_cases i; fin_cases j; rfl)
    (by
      have : (!![(τ : ℂ)]).map Complex.im = Matrix.diagonal fun _ => τ.im := by
        ext i j; fin_cases i; fin_cases j; rfl
      rw [this]
      exact Matrix.PosDef.diagonal fun _ => τ.im_pos)
  rw [nrm1Sq]
  refine (setAverage_eq_of_fundamental (epsilon_fundamental ha h) hb
    (f := fun z => ‖canTheta a τ z‖ ^ 2 * Real.exp (-π * ‖z‖ ^ 2 / area Λ))
    (weight_invariant (thetaTranslation_canonicalOddTheta_lattice ha h))).trans ?_
  rw [setAverage_fundamentalDomain]
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun p => ?_))
    (key.trans (by simp))
  have e : ∑ i, p i • b i = a * (p (.inl 0) + p (.inr 0) * τ) := by
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, h1, h2, Complex.real_smul]
    ring
  have e2 : (fun i => (((![1 / 2] : Fin 1 → ℝ) i : ℝ) : ℂ)) = ![1 / 2] := by
    ext i; fin_cases i; simp
  have e3 : ((fun i => (p (.inl i) : ℂ)) + (!![(τ : ℂ)]).mulVec fun i => (p (.inr i) : ℂ)) =
      ![(p (.inl 0) : ℂ) + p (.inr 0) * τ] := by
    ext i; fin_cases i; simp [Matrix.mulVec, dotProduct, mul_comm]
  simp only [e, e2, e3, canTheta, mul_div_cancel_left₀ _ ha, oddTheta,
    LatticeAreaBound.area_eq ha h]
  rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add,
    mul_comm]
  congr 2
  have hy := τ.im_ne_zero
  have hn := norm_ne_zero_iff.2 ha
  rw [show (2 * (τ.im : ℂ)) = ((2 * τ.im : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re,
    norm_mul, mul_pow, Complex.sq_norm (_ + _)]
  simp [Complex.normSq_apply, Matrix.mulVec, dotProduct, sq]
  field_simp
  ring

end

theorem odd_theta_norm_sigma_star : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → nrm1Sq Λ (sgStar Λ) ^ 2 = 2 * Real.pi ^ 2 / area Λ ∧ ∀ t, U1 Λ t (sgStar Λ) 0 ≠ 0 → nrm1Sq Λ (GL3Theta.th0 Λ t) = nrm1Sq Λ (sgStar Λ) / ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 := by
  intro Λ hΛ hd
  obtain ⟨⟨-, -, -, hU⟩, -, huniq, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨w₁, w₂, hi, hΛ⟩ := hΛ
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨a, τ, ha, h'⟩ := exists_lattice_eq_mul_tau L
  have h := fun x => (hL x).trans (h' x)
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have hπ := Real.pi_pos
  refine ⟨?_, fun t _ => ?_⟩
  · rw [LatticeAreaBound.discr_eq L _ hL, ← latticeCurve_Δ,
      latticeCurve_Δ_eq_discriminant ha h'] at hd
    have hπ' : ‖(2 * π : ℂ)‖ = 2 * π := by simp [hπ.le]
    have e := congrArg norm hd
    rw [norm_mul, norm_pow, norm_div, hπ', norm_one, div_pow, div_mul_eq_mul_div,
      div_eq_one_iff_eq (by positivity)] at e
    have j := congrArg norm (JacobiDeriv.deriv_thetaChar_pow_eight τ)
    rw [norm_mul, norm_pow, norm_pow, hπ'] at j
    change ‖deriv (oddTheta τ) 0‖ ^ 8 = _ at j
    have hG : canTheta a τ = fun z => deriv (canTheta a τ) 0 * sgStar Λ z :=
      funext (huniq _ (differentiable_canTheta a τ) (thetaTranslation_canonicalOddTheta_lattice ha h))
    have k := odd_theta_norm_canonical ha h
    rw [hG, odd_theta_norm_smul, deriv_canTheta, norm_div] at k
    set d := ‖deriv (oddTheta τ) 0‖
    have hd4 : d ^ 4 * (2 * π) ^ 2 = ‖a‖ ^ 6 := by
      refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
      linear_combination (2 * π) ^ 4 * j + e
    have k2 : ((d / ‖a‖) ^ 2 * nrm1Sq Λ (sgStar Λ)) ^ 2 = (2 * τ.im)⁻¹ := by
      rw [k, inv_pow, Real.sq_sqrt (by positivity)]
    rw [LatticeAreaBound.area_eq ha h]
    generalize nrm1Sq Λ (sgStar Λ) = N at k2 ⊢
    field_simp at k2 ⊢
    refine mul_left_cancel₀ (pow_pos hn 4).ne' ?_
    linear_combination 2 * π ^ 2 * k2 - N ^ 2 * τ.im * hd4
  · have : GL3Theta.th0 Λ t = fun z => (U1 Λ t (sgStar Λ) 0)⁻¹ * U1 Λ t (sgStar Λ) z :=
      funext fun z => div_eq_inv_mul _ _
    rw [this, odd_theta_norm_smul, odd_theta_norm_translate ha h hU, norm_inv, inv_pow, div_eq_inv_mul]

end GlobalTheory.OddThetaNorm
