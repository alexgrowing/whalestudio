import Formalism.HermitianCurvature.StatementG

open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.G8

instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

theorem muPi_eq (β : ℂ) (ι : Type) [Fintype ι] :
    muPi β ι = (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  unfold muPi
  refine Measure.pi_eq (μ := fun _ : ι => mu β) fun s hs => ?_
  rw [volume_pi]
  simp only [mu, Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem normSq_det_unitary (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : Complex.normSq W.det = 1 := by
  have h1 := (Unitary.mem_iff.1 (Matrix.det_of_mem_unitary hW)).1
  have h2 : ((Complex.normSq W.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h1
  exact_mod_cast h2

theorem volume_unitary (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Measure.map (fun x : Fin d → ℂ => W *ᵥ x) (volume : Measure (Fin d → ℂ)) = volume := by
  have hdet : LinearMap.det ((Matrix.toLin' W).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      normSq_det_unitary d W hW]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin d → ℂ))
    (f := (Matrix.toLin' W).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h
  have hf : (fun x : Fin d → ℂ => W *ᵥ x) = ⇑((Matrix.toLin' W).restrictScalars ℝ) := by
    ext x; simp
  rw [hf, h]; simp

theorem measurable_mulVec (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) :
    Measurable (fun x : Fin d → ℂ => W *ᵥ x) := by
  have : Continuous (fun x : Fin d → ℂ => W *ᵥ x) := by fun_prop
  exact this.measurable

theorem unitaryInvariant : UnitaryInvariant := by
  intro d β W hW
  refine ⟨measurable_mulVec d W, ?_⟩
  rw [muPi_eq, Measure.map_smul, volume_unitary d W hW]

theorem cpow_half_mul (u : ℂ) (hu : 0 < u.re) (R : ℝ) (hR : 0 < R) :
    ((Real.pi : ℂ) / u) ^ (1 / 2 : ℂ) * ((Real.pi : ℂ) / ((R : ℂ) / u)) ^ (1 / 2 : ℂ) =
      ((Real.pi / Real.sqrt R : ℝ) : ℂ) := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have harg : u.arg ≠ Real.pi := by
    intro h; have := (Complex.arg_eq_pi_iff.1 h).1; linarith
  have hπ := Real.pi_pos
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hπc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  have e1 : (Real.pi : ℂ) / u = ((Real.pi : ℝ) : ℂ) * u⁻¹ := div_eq_mul_inv _ _
  have e2 : (Real.pi : ℂ) / ((R : ℂ) / u) = ((Real.pi / R : ℝ) : ℂ) * u := by
    push_cast; field_simp
  have hpR : 0 < Real.pi / R := by positivity
  rw [e1, e2, Complex.cpow_def_of_ne_zero (mul_ne_zero hπc (inv_ne_zero hu0)),
    Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hpR.ne') hu0), ← Complex.exp_add,
    Complex.log_ofReal_mul hπ (inv_ne_zero hu0), Complex.log_ofReal_mul hpR hu0, Complex.log_inv _ harg]
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have e3 : Real.pi / Real.sqrt R = Real.exp (Real.log Real.pi - Real.log R / 2) := by
    rw [← Real.log_sqrt hR.le, ← Real.log_div hπ.ne' hs.ne', Real.exp_log (by positivity)]
  rw [e3, Real.log_div hπ.ne' hR.ne']
  push_cast
  congr 1
  ring

noncomputable def gK (δ p q : ℝ) (z : ℝ × ℝ) : ℂ :=
  Complex.exp (-((δ : ℂ) + Complex.I * p) * (z.2 : ℂ) ^ 2 + (-2 * Complex.I * q * z.1) * (z.2 : ℂ) +
    -((δ : ℂ) - Complex.I * p) * (z.1 : ℂ) ^ 2)

theorem norm_gK (δ p q : ℝ) (z : ℝ × ℝ) :
    ‖gK δ p q z‖ = Real.exp (-δ * z.1 ^ 2) * Real.exp (-δ * z.2 ^ 2) := by
  rw [gK, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [pow_two]
  ring

theorem integrable_gK (δ p q : ℝ) (hδ : 0 < δ) : Integrable (gK δ p q) (volume : Measure (ℝ × ℝ)) := by
  have h1 : Integrable (fun z : ℝ × ℝ => Real.exp (-δ * z.1 ^ 2) * Real.exp (-δ * z.2 ^ 2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (integrable_exp_neg_mul_sq hδ).mul_prod (integrable_exp_neg_mul_sq hδ)
  refine h1.mono' ?_ (Filter.Eventually.of_forall fun z => (norm_gK δ p q z).le)
  have : Continuous (gK δ p q) := by unfold gK; fun_prop
  exact this.aestronglyMeasurable

theorem integral_gK (δ p q : ℝ) (hδ : 0 < δ) :
    ∫ z : ℝ × ℝ, gK δ p q z = ((Real.pi / Real.sqrt (δ ^ 2 + p ^ 2 + q ^ 2) : ℝ) : ℂ) := by
  have hR : 0 < δ ^ 2 + p ^ 2 + q ^ 2 := by positivity
  set u : ℂ := (δ : ℂ) + Complex.I * p with hu
  have hure : u.re = δ := by simp [hu]
  have hu0 : u ≠ 0 := by intro h; rw [h] at hure; simp at hure; exact hδ.ne hure
  rw [Measure.volume_eq_prod, integral_prod _ (integrable_gK δ p q hδ)]
  have hin : ∀ x : ℝ, ∫ y : ℝ, gK δ p q (x, y) =
      ((Real.pi : ℂ) / u) ^ (1 / 2 : ℂ) *
        Complex.exp (-(((δ ^ 2 + p ^ 2 + q ^ 2 : ℝ) : ℂ) / u) * (x : ℂ) ^ 2) := by
    intro x
    show ∫ y : ℝ, Complex.exp (-u * (y : ℂ) ^ 2 + (-2 * Complex.I * q * x) * (y : ℂ) +
      -((δ : ℂ) - Complex.I * p) * (x : ℂ) ^ 2) = _
    rw [integral_cexp_quadratic (by rw [Complex.neg_re, hure]; linarith)]
    rw [neg_neg]
    congr 2
    have hconj : ((δ : ℂ) - Complex.I * p) * u = (δ : ℂ) ^ 2 + (p : ℂ) ^ 2 := by
      rw [hu]; linear_combination (-(p:ℂ)^2) * Complex.I_sq
    obtain ⟨v, hv⟩ : ∃ v : ℂ, v = (δ : ℂ) - Complex.I * p := ⟨_, rfl⟩
    rw [← hv] at hconj ⊢
    clear_value u
    push_cast
    field_simp
    linear_combination (-4 * (x:ℂ)^2) * hconj + (4 * (q:ℂ)^2 * (x:ℂ)^2) * Complex.I_sq
  simp_rw [hin]
  rw [integral_const_mul, integral_gaussian_complex, cpow_half_mul u (by rw [hure]; exact hδ) _ hR]
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero, hure]
  have : 0 < Complex.normSq u := Complex.normSq_pos.2 hu0
  positivity

theorem gaussOneDamped : GaussOneDamped := by
  intro β a δ hδ
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ, γ = β * a / 2 := ⟨_, rfl⟩
  have hint : ∀ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (a * w ^ 2 / 2) =
      gK δ γ.re γ.im (Complex.measurableEquivRealProd w) := by
    intro w
    have h1 : (β * (a * w ^ 2 / 2)).re =
        γ.re * (w.re ^ 2 - w.im ^ 2) - γ.im * (2 * w.re * w.im) := by
      have : β * (a * w ^ 2 / 2) = γ * (w * w) := by rw [hγ]; ring
      rw [this]; simp only [Complex.mul_re, Complex.mul_im]; ring
    rw [psi, gK, Complex.ofReal_exp, ← Complex.exp_add, h1, Complex.sq_norm, Complex.normSq_apply,
      Complex.measurableEquivRealProd_apply]
    congr 1
    push_cast
    ring
  have hn : γ.re ^ 2 + γ.im ^ 2 = ‖β‖ ^ 2 * ‖a‖ ^ 2 / 4 := by
    have : ‖γ‖ ^ 2 = γ.re ^ 2 + γ.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← this, hγ, norm_div, norm_mul]; simp; ring
  simp_rw [hint]
  rw [mu, integral_smul_nnreal_measure,
    Complex.volume_preserving_equiv_real_prod.integral_comp
      (MeasurableEquiv.measurableEmbedding _) (gK δ γ.re γ.im), integral_gK δ _ _ hδ,
    NNReal.smul_def, Real.coe_toNNReal _ (by positivity), Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  have hR : 0 < δ ^ 2 + γ.re ^ 2 + γ.im ^ 2 := by positivity
  have e : 4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2 = 2 ^ 2 * (δ ^ 2 + γ.re ^ 2 + γ.im ^ 2) := by
    linear_combination (-4 : ℝ) * hn
  rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hs : 0 < Real.sqrt (δ ^ 2 + γ.re ^ 2 + γ.im ^ 2) := Real.sqrt_pos.2 hR
  have := Real.pi_pos
  field_simp

theorem gaussOne_of_damped (h : GaussOneDamped) : GaussOne := by
  intro β a hβ ha
  have h1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), ((‖β‖ / Real.sqrt (4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2) : ℝ) : ℂ) =
      ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (a * w ^ 2 / 2) ∂(mu β) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ using (h β a δ hδ).symm
  refine Filter.Tendsto.congr' h1 ?_
  have hb : 0 < ‖β‖ := norm_pos_iff.2 hβ
  have hab : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hc : ContinuousAt (fun δ:ℝ => ‖β‖ / Real.sqrt (4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2)) 0 := by
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    have : 0 < 4 * (0:ℝ) ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2 := by positivity
    exact (Real.sqrt_pos.2 this).ne'
  have h2 := (Complex.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  convert h2 using 2
  simp only [Function.comp]
  congr 1
  have : 4 * (0:ℝ) ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2 = (‖β‖ * ‖a‖) ^ 2 := by ring
  show ‖a‖⁻¹ = ‖β‖ / Real.sqrt (4 * (0:ℝ) ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2)
  rw [this, Real.sqrt_sq (by positivity)]
  field_simp

theorem psi_add (β x y : ℂ) : psi β (x + y) = psi β x * psi β y := by
  simp only [psi, mul_add, Complex.add_re, Complex.ofReal_add, Complex.exp_add]

theorem psi_zero (β : ℂ) : psi β 0 = 1 := by simp [psi]

theorem psi_sum {ι : Type} (β : ℂ) (s : Finset ι) (f : ι → ℂ) :
    psi β (∑ k ∈ s, f k) = ∏ k ∈ s, psi β (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [psi_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, psi_add, ih]

theorem continuous_psi (β : ℂ) : Continuous (psi β) := by
  unfold psi; fun_prop

theorem transpose_mem_unitary (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : Wᵀ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff'.1 hW
  have e : star Wᵀ = (star W)ᵀ := by
    ext i j; simp [Matrix.star_apply]
  rw [e, ← Matrix.transpose_mul, h, Matrix.transpose_one]

theorem sum_norm_sq_unitary (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d → ℂ) :
    ∑ k, ‖(U *ᵥ x) k‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by
  have e : ∀ y : Fin d → ℂ, ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
    intro y
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]; rfl
  have h := Matrix.mem_unitaryGroup_iff'.1 hU
  have : ((∑ k, ‖(U *ᵥ x) k‖ ^ 2 : ℝ) : ℂ) = ((∑ k, ‖x k‖ ^ 2 : ℝ) : ℂ) := by
    rw [e, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, h, Matrix.one_mulVec]
  exact_mod_cast this

theorem quad_form_takagi (d : ℕ) (W D : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    x ⬝ᵥ ((W * D * Wᵀ) *ᵥ x) = (Wᵀ *ᵥ x) ⬝ᵥ (D *ᵥ (Wᵀ *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

noncomputable def diagF (β : ℂ) (d : ℕ) (σ : Fin d → ℝ) (t : ℂ) (δ : ℝ) (y : Fin d → ℂ) : ℂ :=
  ((Real.exp (-δ * ∑ k, ‖y k‖ ^ 2) : ℝ) : ℂ) *
    psi β ((y ⬝ᵥ (Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) *ᵥ y)) / (2 * t))

theorem continuous_diagF (β : ℂ) (d : ℕ) (σ : Fin d → ℝ) (t : ℂ) (δ : ℝ) :
    Continuous (diagF β d σ t δ) := by
  unfold diagF
  refine Continuous.mul (by fun_prop) ((continuous_psi β).comp ?_)
  fun_prop

theorem diagF_eq_prod (β : ℂ) (d : ℕ) (σ : Fin d → ℝ) (t : ℂ) (δ : ℝ) (y : Fin d → ℂ) :
    diagF β d σ t δ y =
      ∏ k, (((Real.exp (-δ * ‖y k‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * (y k) ^ 2 / 2)) := by
  rw [Finset.prod_mul_distrib, ← psi_sum, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum, diagF]
  congr 2
  simp only [dotProduct, Matrix.mulVec_diagonal, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_mul_eq_mul_div, div_div, mul_comm t 2]
  congr 1
  ring

theorem gaussInt_takagi (hU : UnitaryInvariant) (d : ℕ) (β t : ℂ) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) (σ : Fin d → ℝ) (δ : ℝ) :
    gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t δ =
      ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) := by
  have hWt := transpose_mem_unitary d W hW
  have hmp := hU d β Wᵀ hWt
  have h1 : gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t δ =
      ∫ x : Fin d → ℂ, diagF β d σ t δ (Wᵀ *ᵥ x) ∂(muPi β (Fin d)) := by
    unfold gaussInt diagF
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [quad_form_takagi, sum_norm_sq_unitary d Wᵀ hWt x]
  rw [h1, ← integral_map hmp.measurable.aemeasurable
    (continuous_diagF β d σ t δ).aestronglyMeasurable, hmp.map_eq]
  simp_rw [diagF_eq_prod]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin d => mu β)
    (fun k w => ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2))

theorem gaussMultiOfOne : GaussMultiOfOne := by
  intro hT hU hG d β t H hβ ht hsym hdet
  obtain ⟨W, hW, σ, hσ, hH⟩ := hT d H hsym
  have hnW : ‖W.det‖ = 1 := by
    have h := normSq_det_unitary d W hW
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg W.det, sq_nonneg (‖W.det‖ - 1)]
  have hdH : H.det = W.det * (∏ k, ((σ k : ℝ) : ℂ)) * W.det := by
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  have hσ0 : ∀ k, σ k ≠ 0 := by
    intro k hk
    apply hdet
    rw [hdH, Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; simp)]
    simp
  have hkey : gaussInt β d H t = fun δ => ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) *
      psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) := by
    funext δ; rw [hH]; exact gaussInt_takagi hU d β t W hW σ δ
  have hlim : ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ) = ∏ k : Fin d, (((‖(σ k : ℂ) / t‖)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    congr 1
    rw [hdH, norm_mul, norm_mul, hnW, norm_prod]
    simp only [norm_div, inv_div, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, one_mul, mul_one]
  rw [hkey, hlim]
  refine tendsto_finsetProd _ fun k _ => ?_
  exact gaussOne_of_damped hG β _ hβ (div_ne_zero (by exact_mod_cast hσ0 k) ht)

theorem gaussHessOfMulti : GaussHessOfMulti := by
  intro hG hD m β t z hβ ht hz
  have hdet : (z⁻¹ • (1 + Matrix.of fun _ _ => (1 : ℂ)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det ≠ 0 := by
    rw [hD m z]
    have : ((m:ℂ)+2) ≠ 0 := by
      have : ((m:ℂ)+2) = ((m+2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (Nat.succ_ne_zero (m+1))
    exact mul_ne_zero this (pow_ne_zero _ (inv_ne_zero hz))
  have hs : (z⁻¹ • (1 + Matrix.of fun _ _ => (1 : ℂ)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).IsSymm := by
    ext i j; simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm, mul_add]
  have h := hG (m+1) β t _ hβ ht hs hdet
  rw [hD m z] at h
  convert h using 3
  have h2 : ‖(m:ℂ)+2‖ = (m:ℝ)+2 := by
    have : ((m:ℂ)+2) = (((m:ℝ)+2 : ℝ):ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, norm_pow, norm_inv, h2]
  have : 0 < ‖z‖ := norm_pos_iff.2 hz
  field_simp
  rw [← mul_pow]; simp [this.ne']

end Formalism.FourierDecayAlt.P.G8

namespace Formalism.FourierDecayAlt.P

theorem gaussian_one_damped : Formalism.FourierDecayAlt.G.GaussOneDamped := G8.gaussOneDamped

theorem gaussian_one_dim : Formalism.FourierDecayAlt.G.GaussOne := G8.gaussOne_of_damped G8.gaussOneDamped

theorem gaussian_multi_of_one : Formalism.FourierDecayAlt.G.GaussMultiOfOne := G8.gaussMultiOfOne

theorem gaussian_hessian_of_multi : Formalism.FourierDecayAlt.G.GaussHessOfMulti := G8.gaussHessOfMulti

theorem unitary_invariant_gaussian : Formalism.FourierDecayAlt.G.UnitaryInvariant := G8.unitaryInvariant

end Formalism.FourierDecayAlt.P
