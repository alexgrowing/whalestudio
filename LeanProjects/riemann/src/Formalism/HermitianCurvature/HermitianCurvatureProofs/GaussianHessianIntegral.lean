import Formalism.HermitianCurvature.StatementG

section Factorisation

open scoped InnerProductSpace ComplexConjugate
open Module

namespace Formalism.FourierDecayAlt.P.G9

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_takagi_vector (T : E →ₗ⋆[ℂ] E) (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪T y, x⟫_ℂ)
    (S : Submodule ℂ E) (hS : ∀ x ∈ S, T x ∈ S) (hne : S ≠ ⊥) :
    ∃ v ∈ S, ∃ σ : ℝ, 0 ≤ σ ∧ ‖v‖ = 1 ∧ T v = (σ : ℂ) • v := by
  let A : E →ₗ[ℂ] E := T.comp T
  have hA : ∀ x ∈ S, A x ∈ S := fun x hx => hS _ (hS _ hx)
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (A.restrict hA)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx0 : (x : E) ≠ 0 := by simpa using hx.2
  have hAx : T (T x) = μ • (x : E) := by
    have h := congrArg Subtype.val hx.apply_eq_smul
    simpa [A] using h
  have hnx : 0 < ‖(x : E)‖ := norm_pos_iff.2 hx0
  have h1 : conj μ * ((‖(x:E)‖ : ℂ) ^ 2) = ((‖T x‖ : ℂ) ^ 2) := by
    have h : ⟪T (T x), (x:E)⟫_ℂ = ⟪T x, T x⟫_ℂ := hT _ _
    rw [hAx, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    simpa using h
  set σ : ℝ := ‖T x‖ / ‖(x:E)‖ with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hμσ : μ = (σ : ℂ) ^ 2 := by
    have hxc : ((‖(x:E)‖ : ℂ)) ≠ 0 := by exact_mod_cast hnx.ne'
    have h2 : conj μ = (σ : ℂ) ^ 2 := by
      rw [hσ]; push_cast; field_simp; exact h1
    have h3 := congrArg conj h2
    simpa using h3
  have key : ∀ w ∈ S, w ≠ 0 → T w = (σ : ℂ) • w →
      ∃ v ∈ S, ∃ σ : ℝ, 0 ≤ σ ∧ ‖v‖ = 1 ∧ T v = (σ : ℂ) • v := by
    intro w hw hw0 hTw
    refine ⟨((‖w‖⁻¹ : ℝ) : ℂ) • w, S.smul_mem _ hw, σ, hσ0, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
    · rw [T.map_smulₛₗ, hTw, Complex.conj_ofReal, smul_comm]
  by_cases hy : T x + (σ : ℂ) • (x : E) = 0
  · refine key (Complex.I • (x : E)) (S.smul_mem _ x.2) (smul_ne_zero Complex.I_ne_zero hx0) ?_
    have hTx : T x = -((σ : ℂ) • (x : E)) := eq_neg_of_add_eq_zero_left hy
    rw [T.map_smulₛₗ, hTx, Complex.conj_I, smul_neg, neg_smul, neg_neg, smul_comm]
  · refine key _ (S.add_mem (hS _ x.2) (S.smul_mem _ x.2)) hy ?_
    rw [map_add, T.map_smulₛₗ, hAx, hμσ, Complex.conj_ofReal, smul_add, smul_smul, pow_two, add_comm]

theorem exists_takagi_family (T : E →ₗ⋆[ℂ] E) (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪T y, x⟫_ℂ) :
    ∀ (n : ℕ) (S : Submodule ℂ E), finrank ℂ S = n → (∀ x ∈ S, T x ∈ S) →
      ∃ (e : Fin n → E) (σ : Fin n → ℝ), Orthonormal ℂ e ∧ (∀ i, e i ∈ S) ∧ (∀ i, 0 ≤ σ i) ∧
        ∀ i, T (e i) = (σ i : ℂ) • e i := by
  intro n
  induction n with
  | zero =>
    intro S _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro S hn hS
    have hne : S ≠ ⊥ := by
      rintro rfl
      simp at hn
    obtain ⟨v, hvS, σ₀, hσ₀, hv1, hTv⟩ := exists_takagi_vector T hT S hS hne
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv1
    have hle : (ℂ ∙ v) ≤ S := (Submodule.span_singleton_le_iff_mem _ _).2 hvS
    have hfr : finrank ℂ ((ℂ ∙ v)ᗮ ⊓ S : Submodule ℂ E) = n := by
      have h := Submodule.finrank_add_inf_finrank_orthogonal hle
      rw [finrank_span_singleton hv0, hn] at h
      omega
    have hS' : ∀ x ∈ ((ℂ ∙ v)ᗮ ⊓ S : Submodule ℂ E), T x ∈ ((ℂ ∙ v)ᗮ ⊓ S : Submodule ℂ E) := by
      intro x hx
      refine ⟨?_, hS _ hx.2⟩
      have hx1 : ⟪v, x⟫_ℂ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hx.1
      refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
      rw [hT, hTv, inner_smul_left, hx1, mul_zero]
    obtain ⟨e, σ, he, heS, hσ, hTe⟩ := ih _ hfr hS'
    have hve : ∀ i, ⟪v, e i⟫_ℂ = 0 := fun i =>
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (heS i).1
    have hev : ∀ i, ⟪e i, v⟫_ℂ = 0 := fun i =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (heS i).1
    refine ⟨Fin.cons v e, Fin.cons σ₀ σ, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hv1
      · simpa using he.1 j
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using hve j
      | succ i =>
        induction j using Fin.cases with
        | zero => simpa using hev i
        | succ j =>
          have : i ≠ j := fun h => hij (by rw [h])
          simpa using he.2 this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvS
      · simpa using (heS j).2
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hσ₀
      · simpa using hσ j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hTv
      · simpa using hTe j

noncomputable def takMap {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d) →ₗ⋆[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun x := WithLp.toLp 2 (H.mulVec (star (WithLp.ofLp x)))
  map_add' x y := by
    simp [Matrix.mulVec_add]
  map_smul' c x := by
    simp [Matrix.mulVec_smul]

theorem takMap_apply {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    takMap H x i = ∑ j, H i j * conj (x j) := by
  simp [takMap, Matrix.mulVec, dotProduct]

theorem takMap_symm {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsSymm)
    (x y : EuclideanSpace ℂ (Fin d)) : ⟪takMap H x, y⟫_ℂ = ⟪takMap H y, x⟫_ℂ := by
  simp only [PiLp.inner_apply, takMap_apply, RCLike.inner_apply, map_sum, map_mul, Complex.conj_conj,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply i j]
  ring

end Formalism.FourierDecayAlt.P.G9

theorem Formalism.FourierDecayAlt.P.takagi_factorization : Formalism.FourierDecayAlt.G.Takagi := by
  intro d H hH
  obtain ⟨e, σ, he, -, hσ, hTe⟩ := Formalism.FourierDecayAlt.P.G9.exists_takagi_family (Formalism.FourierDecayAlt.P.G9.takMap H)
    (Formalism.FourierDecayAlt.P.G9.takMap_symm H hH) d ⊤ (by simp) (fun _ _ => Submodule.mem_top)
  set W : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => e j i with hW
  have h1 : star W * W = 1 := by
    ext i j
    have h := (orthonormal_iff_ite.1 he) i j
    rw [PiLp.inner_apply] at h
    simp only [RCLike.inner_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hW, Matrix.star_apply, mul_comm]
  have h2 : W * star W = 1 := mul_eq_one_comm.1 h1
  have h3 : H * W.map conj = W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) := by
    ext i j
    have h := congrFun (congrArg WithLp.ofLp (hTe j)) i
    have h' : Formalism.FourierDecayAlt.P.G9.takMap H (e j) i = (σ j : ℂ) * e j i := by simpa using h
    rw [Formalism.FourierDecayAlt.P.G9.takMap_apply] at h'
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, hW, Matrix.of_apply]
    rw [h', mul_comm]
  have h4 : W.map conj * W.transpose = 1 := by
    have h := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h
    rw [← h]
    congr 1
  refine ⟨W, Matrix.mem_unitaryGroup_iff.2 h2, σ, hσ, ?_⟩
  rw [← h3, Matrix.mul_assoc, h4, Matrix.mul_one]

end Factorisation

section OneVariable

open Formalism.FourierDecayAlt.G MeasureTheory

namespace Formalism.FourierDecayAlt.P.G9

theorem map_mul_vol (α : ℂ) (hα : α ≠ 0) :
    Measure.map (fun ρ : ℂ => α * ρ) (volume : Measure ℂ) = ENNReal.ofReal ((‖α‖ ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ α) = ‖α‖ ^ 2 := by
    have h1 := Algebra.norm_complex_apply α
    rw [Algebra.norm_apply] at h1
    rw [← Complex.normSq_eq_norm_sq, ← h1]
    rfl
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ α) (by rw [hdet]; positivity)
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h

theorem integral_comp_mul (α : ℂ) (hα : α ≠ 0) (G : ℂ → ℂ) :
    ∫ ξ : ℂ, G (α * ξ) = ((‖α‖ ^ 2)⁻¹ : ℝ) • ∫ η : ℂ, G η := by
  have h := map_mul_vol α hα
  have he : MeasurableEmbedding (fun ρ : ℂ => α * ρ) :=
    (Homeomorph.mulLeft₀ α hα).measurableEmbedding
  rw [← he.integral_map, h, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

theorem sqrt_prod (δ r : ℝ) (hδ : 0 < δ) :
    ((Real.pi : ℂ) / ((δ : ℂ) - r * Complex.I)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / ((δ : ℂ) + r * Complex.I)) ^ (1 / 2 : ℂ) =
      ((Real.pi / Real.sqrt (δ ^ 2 + r ^ 2) : ℝ) : ℂ) := by
  set b : ℂ := (δ : ℂ) - r * Complex.I with hb
  have hcb : (starRingEnd ℂ) b = (δ : ℂ) + r * Complex.I := by
    simp [hb]
  have hbre : b.re = δ := by simp [hb]
  have hbim : b.im = -r := by simp [hb]
  have hb0 : b ≠ 0 := by
    intro h; rw [h] at hbre; simp at hbre; linarith
  set z : ℂ := (Real.pi : ℂ) / b with hz
  have hcz : (starRingEnd ℂ) z = (Real.pi : ℂ) / ((δ : ℂ) + r * Complex.I) := by
    rw [hz, map_div₀, hcb, Complex.conj_ofReal]
  have hzre : 0 < z.re := by
    rw [hz, Complex.div_re]
    have : 0 < Complex.normSq b := Complex.normSq_pos.2 hb0
    simp only [Complex.ofReal_re, Complex.ofReal_im, hbre, zero_mul, zero_div, add_zero]
    have := Real.pi_pos
    positivity
  have harg : z.arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.1 h).1
    linarith
  rw [← hcz, Complex.conj_cpow z _ harg]
  have h12 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.conj_ofReal]
  rw [h12, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : ‖z ^ (1 / 2 : ℂ)‖ = ‖z‖ ^ (1 / 2 : ℝ) := by
    have := Complex.norm_cpow_real z (1 / 2 : ℝ)
    rw [← this]; congr 2; push_cast; ring
  rw [h3, ← Real.sqrt_eq_rpow, Real.sq_sqrt (norm_nonneg _)]
  congr 1
  rw [hz, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply, hbre, hbim]
  congr 1; ring

theorem core (δ r : ℝ) (hδ : 0 < δ) :
    ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((r * (w ^ 2).re : ℝ) : ℂ)) =
      ((Real.pi / Real.sqrt (δ ^ 2 + r ^ 2) : ℝ) : ℂ) := by
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  have h : ∀ p : ℝ × ℝ,
      ((Real.exp (-δ * ‖Complex.measurableEquivRealProd.symm p‖ ^ 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((r * ((Complex.measurableEquivRealProd.symm p) ^ 2).re : ℝ) : ℂ)) =
      Complex.exp (-((δ : ℂ) - r * Complex.I) * (p.1 : ℂ) ^ 2) *
        Complex.exp (-((δ : ℂ) + r * Complex.I) * (p.2 : ℂ) ^ 2) := by
    rintro ⟨x, y⟩
    have e : Complex.measurableEquivRealProd.symm (x, y) = ⟨x, y⟩ := rfl
    rw [e, ← Complex.normSq_eq_norm_sq, Complex.normSq_mk, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only [pow_two, Complex.mul_re]
    push_cast
    ring
  simp_rw [h]
  rw [Measure.volume_eq_prod, integral_prod_mul (fun x : ℝ => Complex.exp (-((δ : ℂ) - r * Complex.I) * (x : ℂ) ^ 2))
    (fun y : ℝ => Complex.exp (-((δ : ℂ) + r * Complex.I) * (y : ℂ) ^ 2)),
    integral_gaussian_complex (by simpa using hδ), integral_gaussian_complex (by simpa using hδ)]
  exact sqrt_prod δ r hδ

theorem exists_rot (γ : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ γ * u ^ 2 = (‖γ‖ : ℂ) := by
  refine ⟨Complex.exp (-(γ.arg / 2 : ℝ) * Complex.I), ?_, ?_⟩
  · have : (-((γ.arg / 2 : ℝ) : ℂ) * Complex.I) = ((-(γ.arg / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  · have h0 := Complex.norm_mul_exp_arg_mul_I γ
    generalize γ.arg = θ at h0 ⊢
    rw [← h0, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    have : (θ : ℂ) * Complex.I + ((2 : ℕ) : ℂ) * (-((θ / 2 : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero, mul_one, h0]

theorem gen (δ : ℝ) (γ : ℂ) (hδ : 0 < δ) :
    ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (((γ * w ^ 2).re : ℝ) : ℂ)) =
      ((Real.pi / Real.sqrt (δ ^ 2 + ‖γ‖ ^ 2) : ℝ) : ℂ) := by
  obtain ⟨u, hu, hγ⟩ := exists_rot γ
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h := integral_comp_mul u hu0 (fun w : ℂ => ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (((γ * w ^ 2).re : ℝ) : ℂ)))
  rw [hu] at h
  simp only [one_pow, inv_one, one_smul] at h
  rw [← h, ← core δ ‖γ‖ hδ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  have e : γ * (u * w) ^ 2 = (‖γ‖ : ℂ) * w ^ 2 := by rw [← hγ]; ring
  rw [e, norm_mul, hu, one_mul, Complex.re_ofReal_mul]

theorem gaussOneDamped : Formalism.FourierDecayAlt.G.GaussOneDamped := by
  intro β a δ hδ
  have hc : 0 ≤ ‖β‖ / (2 * Real.pi) := by positivity
  unfold mu psi
  rw [integral_smul_nnreal_measure]
  have e : ∀ w : ℂ, β * (a * w ^ 2 / 2) = (β * a / 2) * w ^ 2 := fun w => by ring
  simp_rw [e]
  rw [gen δ (β * a / 2) hδ]
  rw [NNReal.smul_def, Real.coe_toNNReal _ hc, Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  have h1 : 4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2 = 2 ^ 2 * (δ ^ 2 + ‖β * a / 2‖ ^ 2) := by
    rw [norm_div, norm_mul]; simp; ring
  rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have h2 : 0 < Real.sqrt (δ ^ 2 + ‖β * a / 2‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have := Real.pi_pos
  field_simp

end Formalism.FourierDecayAlt.P.G9

end OneVariable

section SeveralVariables

open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology

namespace Formalism.FourierDecayAlt.P.G9

theorem norm_det_unitary {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : ‖W.det‖ = 1 := by
  have h := (Unitary.mem_iff.1 (Matrix.det_of_mem_unitary hW)).1
  have h2 : ‖W.det‖ ^ 2 = 1 := by
    have := congrArg norm h
    rw [norm_mul, norm_star, norm_one] at this
    nlinarith [this]
  nlinarith [norm_nonneg W.det, h2]

theorem unitary_mp (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    MeasurePreserving (fun x : Fin d → ℂ => W *ᵥ x) (muPi β (Fin d)) (muPi β (Fin d)) := by
  have hc : Real.toNNReal (‖β‖ / (2 * Real.pi)) ≠ 0 := by
    have : 0 < ‖β‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hβ) (by positivity)
    exact (Real.toNNReal_pos.2 this).ne'
  have : (mu β).IsAddHaarMeasure := by
    unfold mu; exact Measure.IsAddHaarMeasure.nnreal_smul _ hc
  have : (muPi β (Fin d)).IsAddHaarMeasure := by
    unfold muPi; infer_instance
  have hdet : LinearMap.det ((Matrix.toLin' W).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, norm_det_unitary hW, one_pow]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (muPi β (Fin d))
    (f := (Matrix.toLin' W).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  refine ⟨?_, h⟩
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable

theorem sum_normSq_unitary {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d → ℂ) :
    ∑ k, ‖(U *ᵥ x) k‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by
  have key : ∀ y : Fin d → ℂ, ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
    intro y
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.conj_mul' (y k)).symm
  have h : star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    have : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    rw [this, Matrix.one_mulVec]
  exact_mod_cast (key _).trans (h.trans (key x).symm)

theorem transpose_unitary {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : Wᵀ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hW
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h2
  rw [← h2]
  rfl

theorem psi_sum (β : ℂ) {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    psi β (∑ k ∈ s, f k) = ∏ k ∈ s, psi β (f k) := by
  unfold psi
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum]

theorem gaussInt_eq (d : ℕ) (β t : ℂ) (hβ : β ≠ 0) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) (σ : Fin d → ℝ) (δ : ℝ) :
    gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t δ =
      ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) := by
  have hU := transpose_unitary hW
  have hmp := unitary_mp d β hβ Wᵀ hU
  have hinj : Function.Injective (fun x : Fin d → ℂ => Wᵀ *ᵥ x) := by
    intro x y hxy
    have h1 : (Wᵀ)ᴴ * Wᵀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    have := congrArg (fun v => (Wᵀ)ᴴ *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec, h1] using this
  have hemb : MeasurableEmbedding (fun x : Fin d → ℂ => Wᵀ *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurableEmbedding hinj
  have hsf : SigmaFinite (mu β) := by unfold mu; infer_instance
  rw [← integral_fintype_prod_eq_prod (μ := fun _ : Fin d => mu β)
    (fun (k : Fin d) (w : ℂ) => ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2))]
  change _ = ∫ y : Fin d → ℂ, _ ∂(muPi β (Fin d))
  rw [← hmp.integral_comp hemb]
  unfold gaussInt
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Finset.prod_mul_distrib, ← psi_sum, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum,
    sum_normSq_unitary hU]
  congr 2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases ht : t = 0
  · simp [ht]
  · field_simp

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

theorem gaussMulti_of (hT : Takagi) (hG : GaussOneDamped) : GaussMulti := by
  intro d β t H hβ ht hH hdet
  obtain ⟨W, hW, σ, hσ, rfl⟩ := hT d H hH
  have hdW := norm_det_unitary hW
  have hd : ‖(W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ).det‖ = ∏ k, σ k := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, norm_mul, norm_mul, hdW,
      one_mul, mul_one, norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hσ k)]
  have hσ0 : ∀ k, σ k ≠ 0 := by
    intro k hk
    apply hdet
    rw [← norm_eq_zero, hd]
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  have hfun : gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t = fun δ : ℝ =>
      ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) :=
    funext fun δ => gaussInt_eq d β t hβ W hW σ δ
  rw [hfun, hd]
  have hlim : ((‖t‖ ^ d / ∏ k, σ k : ℝ) : ℂ) = ∏ k : Fin d, (((‖(σ k : ℂ) / t‖)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    congr 1
    have : ∀ k : Fin d, (‖(σ k : ℂ) / t‖)⁻¹ = ‖t‖ / σ k := by
      intro k
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hσ k), inv_div]
    simp_rw [this]
    rw [Finset.prod_div_distrib]
    simp
  rw [hlim]
  refine tendsto_finsetProd _ fun k _ => ?_
  exact gaussOne_of_damped hG β _ hβ (div_ne_zero (by exact_mod_cast hσ0 k) ht)

theorem hessDet : HessDet := by
  intro m z
  rw [Matrix.det_smul]
  have h : (Matrix.of fun _ _ => (1:ℂ) : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)
      = Matrix.replicateCol Unit (fun _ : Fin (m+1) => (1:ℂ)) * Matrix.replicateRow Unit (fun _ : Fin (m+1) => (1:ℂ)) := by
    ext i j; simp [Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]
  ring

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

end Formalism.FourierDecayAlt.P.G9

theorem Formalism.FourierDecayAlt.P.gaussian_multi_integral : Formalism.FourierDecayAlt.G.GaussMulti :=
  Formalism.FourierDecayAlt.P.G9.gaussMulti_of Formalism.FourierDecayAlt.P.takagi_factorization Formalism.FourierDecayAlt.P.G9.gaussOneDamped

theorem Formalism.FourierDecayAlt.P.gaussian_hessian_integral : Formalism.FourierDecayAlt.G.GaussHess :=
  Formalism.FourierDecayAlt.P.G9.gaussHessOfMulti Formalism.FourierDecayAlt.P.gaussian_multi_integral Formalism.FourierDecayAlt.P.G9.hessDet

end SeveralVariables
