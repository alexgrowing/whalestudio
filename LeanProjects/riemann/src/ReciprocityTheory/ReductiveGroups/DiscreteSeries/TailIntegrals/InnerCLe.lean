import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergFactsOfInductiveInput

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section chain
variable (k r' : ℕ)

def mw (c : ℂ) : ℝ := min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹

theorem mw_nonneg (c : ℂ) : 0 ≤ mw k r' c :=
  le_min (Real.rpow_nonneg (norm_nonneg _) _) (inv_nonneg.mpr (norm_nonneg _))

theorem mw_meas : Measurable (mw k r') := by
  unfold mw
  exact (measurable_norm.pow_const _).min measurable_norm.inv

theorem weight_eq (s : Fin (1 + r' + 1) → ℝ) (c : ℂ) (hc : c ≠ 0) :
    ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) * ∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l) =
      ENNReal.ofReal (‖c‖ ^ (2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l)) := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h1 : ∀ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l) = ENNReal.ofReal (‖c‖ ^ (-s l)) := fun l => by
    have e : (‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖c‖ := by rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
    rw [e, ENNReal.ofReal_rpow_of_pos hpos]
  simp only [h1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (norm_nonneg _) _),
    ← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _)]
  congr 1
  rw [← Real.rpow_sum_of_pos hpos, ← Real.rpow_natCast, ← Real.rpow_add hpos]
  congr 1
  push_cast
  rw [Finset.sum_neg_distrib]; ring

theorem Qf_le (A C0 : ℝ)
    (hC0 : ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r', EInt k r' A c g ≤ ENNReal.ofReal (C0 * mw k r' c *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)))
    (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (c : ℂ) (hc : c ≠ 0) :
    Qf k r' A s1 μ₁ c ≤
      ENNReal.ofReal (|C0| * mw k r' c) * JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) s1 := by
  unfold Qf JInt
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  have hconc : ∀ᵐ g ∂μ₁, Matrix.of g ∈ GV k r' := by rw [ae_iff]; exact hμ₁.conc
  filter_upwards [hconc] with g hg
  rw [← mul_assoc]
  gcongr ?_ * _
  refine (hC0 c hc _ hg).trans ?_
  have hG : 0 ≤ gN (Matrix.of g) ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A) :=
    Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) _
  rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (mw_nonneg k r' c)),
    show -(A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) = ((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A by ring]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (mw_nonneg k r' c)) hG

theorem scale_c (aw D : ℝ) (hD : 0 < D) :
    ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' (c * (D : ℂ))) =
      ENNReal.ofReal (D ^ (-(aw + 2))) * ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) := by
  have hF : Measurable fun c : ℂ => ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) :=
    (measurable_norm.pow_const _).ennreal_ofReal.mul (mw_meas k r').ennreal_ofReal
  have h1 : ∀ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' (c * (D : ℂ))) =
      ENNReal.ofReal (D ^ (-aw)) * (ENNReal.ofReal (‖D • c‖ ^ aw) * ENNReal.ofReal (mw k r' (D • c))) := by
    intro c
    have e : c * (D : ℂ) = D • c := by rw [Complex.real_smul, mul_comm]
    rw [e, norm_smul, Real.norm_of_nonneg hD.le, Real.mul_rpow hD.le (norm_nonneg _), ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _), ← mul_assoc, ← Real.rpow_add hD, neg_add_cancel,
      Real.rpow_zero, one_mul]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ c : ℂ, ENNReal.ofReal (‖D • c‖ ^ aw) * ENNReal.ofReal (mw k r' (D • c)) =
      ENNReal.ofReal (D ^ (-2 : ℝ)) * ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) := by
    rw [← lintegral_map hF (measurable_const_smul D), Measure.map_addHaar_smul volume hD.ne',
      lintegral_smul_measure]
    congr 2
    rw [Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (pow_pos hD 2)), Real.rpow_neg hD.le,
      Real.rpow_two]
  rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _), ← Real.rpow_add hD]
  congr 3; ring

theorem inner_c_le (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hk : 1 ≤ k) (A C0 : ℝ)
    (hC0 : ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r', EInt k r' A c g ≤ ENNReal.ofReal (C0 * mw k r' c *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)))
    (s : Fin (1 + r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) [SFinite μ₁] (hμ₁ : IsHaarOn (GV k r') μ₁)
    (c : ℂ) (hc : c ≠ 0) :
    ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
      ∫⁻ p : (HPar k r' × HPar k r') × Mt k r',
        ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
          FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2))
        ∂((volume : Measure (HPar k r' × HPar k r')).prod μ₁) ≤
    ENNReal.ofReal (‖c‖ ^ (2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l)) *
      ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
        (ENNReal.ofReal (|C0| * mw k r' (c * (Dx k r' x : ℂ))) *
          JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) (fun l => s (sc r' l))) := by
  obtain ⟨-, -, -, hHI, hHM, -, -, hHA, -, -, -⟩ := heisenbergFacts_of_inductiveInput hB2
  have hos : ∀ (x : HPar k r') (g : Mat k r') (x' : HPar k r'),
      oneStep k r' x c g x' = heis0 k r' (-x.1, -x.2) * w0 k r' c * ιLev k 1 r' g * heis0 k r' x' := by
    intro x g x'; unfold oneStep; rw [hHI]
  have hK : (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) ≠ ⊤ := ENNReal.prod_ne_top fun l _ => by
    rw [← ENNReal.coe_rpow_of_ne_zero (nnnorm_ne_zero_iff.mpr hc)]; exact ENNReal.coe_ne_top
  obtain ⟨H, hHdef⟩ : ∃ H : (HPar k r' × HPar k r') × Mt k r' → ℝ≥0∞, H = fun p =>
      ENNReal.ofReal (gN (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) ^ (-A)) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) := ⟨_, rfl⟩
  have h3 := gN_cont k (1 + r')
  have h2 := lev_cont k r'
  have h1 := heisenberg_map_continuous k r'
  have hHm : Measurable H := by
    have hc1 : Continuous fun p : (HPar k r' × HPar k r') × Mt k r' =>
        gN (heis0 k r' (-p.1.1.1, -p.1.1.2) * w0 k r' c * ιLev k 1 r' (Matrix.of p.2) * heis0 k r' p.1.2) := by
      fun_prop
    have e : H = fun p => ENNReal.ofReal (gN (heis0 k r' (-p.1.1.1, -p.1.1.2) * w0 k r' c *
        ιLev k 1 r' (Matrix.of p.2) * heis0 k r' p.1.2) ^ (-A)) *
          FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) := by
      rw [hHdef]; funext p; rw [hos]
    rw [e]
    exact (hc1.measurable.pow_const _).ennreal_ofReal.mul ((FsE_meas k r' _).comp measurable_snd)
  have hstep1 : ∀ p : (HPar k r' × HPar k r') × Mt k r',
      ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
        FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) =
          (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) * H p := by
    intro p
    have hf : FsE k (1 + r') s (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) =
        (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) * FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) :=
      FsE_oneStep k r' hHA hHM p.1.1 p.1.2 c (Matrix.of p.2) s
    show ENNReal.ofReal (gN (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) ^ (-A)) *
        FsE k (1 + r') s (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) = _
    rw [hf, hHdef]
    ring
  simp_rw [hstep1]
  rw [lintegral_const_mul' _ _ hK, ← mul_assoc, weight_eq k r' s c hc]
  gcongr
  rw [lintegral_prod _ hHm.aemeasurable,
    show (volume : Measure (HPar k r' × HPar k r')) = (volume : Measure (HPar k r')).prod volume from rfl,
    lintegral_prod _ hHm.lintegral_prod_right'.aemeasurable]
  refine lintegral_mono fun x => ?_
  have hsw : Measurable (Function.uncurry fun (x' : HPar k r') (g : Mt k r') => H ((x, x'), g)) :=
    hHm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hsw.aemeasurable]
  have hmx : ∀ g : Mt k r', Measurable fun x' : HPar k r' =>
      ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A)) := by
    intro g
    have e : (fun x' : HPar k r' => ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) =
        fun x' => ENNReal.ofReal (gN (heis0 k r' (-x.1, -x.2) * w0 k r' c * ιLev k 1 r' (Matrix.of g) *
          heis0 k r' x') ^ (-A)) := by
      funext x'; rw [hos]
    rw [e]
    exact ((by fun_prop : Continuous fun x' : HPar k r' => gN (heis0 k r' (-x.1, -x.2) * w0 k r' c *
      ιLev k 1 r' (Matrix.of g) * heis0 k r' x')).measurable.pow_const _).ennreal_ofReal
  have hin : ∀ g : Mt k r', ∫⁻ x', H ((x, x'), g) =
      (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) := by
    intro g; simp only [hHdef]; exact lintegral_mul_const _ (hmx g)
  simp_rw [hin]
  rw [inner_eq k r' hB2 hIW hT hk A s μ₁ hμ₁ x c hc]
  gcongr
  have hG0 := (yx_ga hB2 hIW k r' hk x).1
  have hD : 0 < Dx k r' x := Real.sqrt_pos.mpr hG0
  exact Qf_le k r' A C0 hC0 _ μ₁ hμ₁ _ (mul_ne_zero hc (Complex.ofReal_ne_zero.mpr hD.ne'))

end chain

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
