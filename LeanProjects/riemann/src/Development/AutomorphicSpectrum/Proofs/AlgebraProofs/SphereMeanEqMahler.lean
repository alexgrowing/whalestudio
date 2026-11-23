import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound

open GlobalTheory.CompanionTheory.Ar.HS NumberField MeasureTheory Matrix GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HS.SphereMean

open Metric Set
open scoped ENNReal Pointwise

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

open Classical in

def radial (p : sphere (0 : E) 1) (z : E) : sphere (0 : E) 1 :=
  ⟨if z = 0 then (p : E) else ‖z‖⁻¹ • z, by
    split_ifs with h
    · exact p.2
    · simp [norm_smul, h]⟩

lemma radial_coe_of_ne (p : sphere (0 : E) 1) {z : E} (h : z ≠ 0) :
    (radial p z : E) = ‖z‖⁻¹ • z := by
  simp [radial, h]

lemma measurable_radial (p : sphere (0 : E) 1) : Measurable (radial p) := by
  unfold radial
  apply Measurable.subtype_mk
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((measurable_norm.inv).smul measurable_id)

def ballP (μ : Measure E) : Measure E := (μ (ball 0 1))⁻¹ • μ.restrict (ball 0 1)

instance (μ : Measure E) [μ.IsAddHaarMeasure] : IsProbabilityMeasure (ballP μ) := by
  constructor
  have h0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have h1 : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  simp [ballP, ENNReal.inv_mul_cancel h0 h1]

lemma radial_preimage (p : sphere (0 : E) 1) (s : Set (sphere (0 : E) 1)) :
    (radial p ⁻¹' s ∩ ball 0 1) \ {0} = Ioo (0 : ℝ) 1 • ((↑) '' s : Set E) := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right,
    Set.mem_singleton_iff, Set.mem_smul, Set.mem_Ioo, Set.mem_image]
  constructor
  · rintro ⟨⟨hs, hb⟩, h0⟩
    refine ⟨‖x‖, ⟨norm_pos_iff.2 h0, hb⟩, ‖x‖⁻¹ • x, ⟨radial p x, hs, radial_coe_of_ne p h0⟩, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
  · rintro ⟨r, ⟨hr0, hr1⟩, y, ⟨q, hq, rfl⟩, rfl⟩
    have hq1 : ‖(q : E)‖ = 1 := norm_eq_of_mem_sphere q
    have hne : r • (q : E) ≠ 0 := by
      refine smul_ne_zero hr0.ne' ?_
      intro h
      rw [h, norm_zero] at hq1
      exact zero_ne_one hq1
    refine ⟨⟨?_, ?_⟩, hne⟩
    · have hrad : radial p (r • (q : E)) = q := by
        apply Subtype.ext
        rw [radial_coe_of_ne p hne, norm_smul, hq1, mul_one, Real.norm_eq_abs, abs_of_pos hr0,
          smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
      rw [hrad]
      exact hq
    · rw [norm_smul, hq1, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
      exact hr1

lemma map_radial (μ : Measure E) [μ.IsAddHaarMeasure] (p : sphere (0 : E) 1) :
    (ballP μ).map (radial p) = (μ.toSphere univ)⁻¹ • μ.toSphere := by
  ext s hs
  have hd0 : ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  have hdt : ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hnull : μ (radial p ⁻¹' s ∩ ball 0 1) = μ (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
    rw [← radial_preimage, measure_sdiff_null (measure_singleton 0)]
  rw [Measure.map_apply (measurable_radial p) hs, ballP, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (measurable_radial p hs), hnull, Measure.smul_apply, smul_eq_mul,
    Measure.toSphere_apply' μ hs, Measure.toSphere_apply_univ,
    ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), mul_comm (((Module.finrank ℝ E : ℕ) : ℝ≥0∞)⁻¹) _,
    mul_assoc, ← mul_assoc (((Module.finrank ℝ E : ℕ) : ℝ≥0∞)⁻¹), ENNReal.inv_mul_cancel hd0 hdt, one_mul]

lemma pi_ballP (μ : Measure E) [μ.IsAddHaarMeasure] (k : ℕ) :
    Measure.pi (fun _ : Fin k => ballP μ) =
      ((Measure.pi fun _ : Fin k => μ) (Set.pi univ fun _ => ball (0 : E) 1))⁻¹ •
        (Measure.pi fun _ : Fin k => μ).restrict (Set.pi univ fun _ => ball (0 : E) 1) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (MeasurableSet.univ_pi (fun _ => measurableSet_ball)),
    ← Set.pi_inter_distrib, Measure.pi_pi, Measure.pi_pi]
  simp only [ballP, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_ball]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.inv_pow]

end Cone

section Avg

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma map_normalised {f : X → Y} (hf : MeasurableEmbedding f) {μ : Measure X} {ν : Measure Y}
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha1 : a ≠ ⊤) (hmap : μ.map f = a • ν) (s : Set Y) :
    ((μ (f ⁻¹' s))⁻¹ • μ.restrict (f ⁻¹' s)).map f = (ν s)⁻¹ • ν.restrict s := by
  rw [Measure.map_smul, ← hf.restrict_map, ← hf.map_apply μ s, hmap, Measure.restrict_smul,
    Measure.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl ha1), mul_comm a⁻¹, mul_assoc, ENNReal.inv_mul_cancel ha0 ha1,
    mul_one]

end Avg

section Lin

variable {N k : ℕ}

lemma sum_norm_sq_mulVec {U : Matrix (Fin N) (Fin N) ℂ} (hU : Uᴴ * U = 1) (x : Fin N → ℂ) :
    ∑ i, ‖(U *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have key : star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hsq : ∀ y : Fin N → ℂ, ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
    intro y
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast (hsq (U *ᵥ x)).trans (key.trans (hsq x).symm)

def phi (B C : Matrix (Fin N) (Fin N) ℂ) (h1 : C * B = 1) (h2 : B * C = 1) :
    (Fin k → EuclideanSpace ℂ (Fin N)) ≃ₗ[ℂ] (Fin k × Fin N → ℂ) where
  toFun z p := (B *ᵥ fun a => z p.1 a) p.2
  invFun u i := WithLp.toLp 2 (C *ᵥ fun a => u (i, a))
  map_add' x y := by
    ext p
    exact congrFun (mulVec_add B _ _) p.2
  map_smul' c x := by
    ext p
    exact congrFun (mulVec_smul B c _) p.2
  left_inv z := by
    ext i a
    simp [mulVec_mulVec, h1]
  right_inv u := by
    ext p
    simp [mulVec_mulVec, h2]

lemma norm_phi (h : HermNorm N) {B C : Matrix (Fin N) (Fin N) ℂ} (h1 : C * B = 1) (h2 : B * C = 1)
    (hU : (h.mat * B)ᴴ * (h.mat * B) = 1) (z : Fin k → EuclideanSpace ℂ (Fin N)) (i : Fin k) :
    h.norm (fun j => phi B C h1 h2 z (i, j)) = ‖z i‖ := by
  have e : (fun j => phi B C h1 h2 z (i, j)) = B *ᵥ (fun a => z i a) := by
    funext j
    rfl
  rw [HermNorm.norm, e, Matrix.mulVec_mulVec, sum_norm_sq_mulVec hU, EuclideanSpace.norm_eq]

lemma exists_map_eq_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [FiniteDimensional ℂ Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : X ≃L[ℂ] Y) (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ⊤ ∧ μ.map e = a • ν := by
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  refine ⟨((μ.map e).addHaarScalarFactor ν : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) ν).ne'
  · conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (μ.map e) ν]
    ext s hs
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

end Lin

theorem sphere_mean_eq_mahler : ∀ (N k : ℕ) (h : HermNorm N) (B : Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin k × Fin N) ℂ), 1 ≤ N → f ≠ 0 → (h.mat * B)ᴴ * (h.mat * B) = 1 →
    ∫ t : Fin k → Metric.sphere (0 : EuclideanSpace ℂ (Fin N)) 1,
      Real.log ‖MvPolynomial.eval (fun p : Fin k × Fin N =>
        (B *ᵥ fun a => (t p.1 : EuclideanSpace ℂ (Fin N)) a) p.2) f‖
      ∂(Measure.pi fun _ => Tuple.sphP N) = mahler h k f := by
  intro N k h B f hN hf hU
  have hdet : (h.mat * B).det ≠ 0 := by
    intro h0
    have h3 := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, h0, mul_zero, Matrix.det_one] at h3
    exact zero_ne_one h3
  have hB : IsUnit B.det := by
    rw [Matrix.det_mul] at hdet
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hdet)
  have h1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have h2 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  haveI : Nontrivial (EuclideanSpace ℂ (Fin N)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨p0, hp0⟩ :=
    (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℂ (Fin N))) (r := 1)).2 zero_le_one
  let p : sphere (0 : EuclideanSpace ℂ (Fin N)) 1 := ⟨p0, hp0⟩
  have hsph : Tuple.sphP N = (ballP (volume : Measure (EuclideanSpace ℂ (Fin N)))).map (radial p) := by
    rw [map_radial]
    rfl
  have hmeas : Measurable (fun (z : Fin k → EuclideanSpace ℂ (Fin N)) (i : Fin k) => radial p (z i)) :=
    measurable_pi_lambda _ (fun i => (measurable_radial p).comp (measurable_pi_apply i))
  have hΦ : Continuous (fun t : Fin k → Metric.sphere (0 : EuclideanSpace ℂ (Fin N)) 1 =>
      fun q : Fin k × Fin N => (B *ᵥ fun a => (t q.1 : EuclideanSpace ℂ (Fin N)) a) q.2) := by
    refine continuous_pi (fun q => ?_)
    simp only [Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ (fun a _ => continuous_const.mul ?_)
    fun_prop
  have hF : Measurable (fun t : Fin k → Metric.sphere (0 : EuclideanSpace ℂ (Fin N)) 1 =>
      Real.log ‖MvPolynomial.eval (fun q : Fin k × Fin N =>
        (B *ᵥ fun a => (t q.1 : EuclideanSpace ℂ (Fin N)) a) q.2) f‖) :=
    Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval f).comp hΦ)).measurable
  rw [show (Measure.pi fun _ : Fin k => Tuple.sphP N) =
      (Measure.pi fun _ : Fin k => ballP (volume : Measure (EuclideanSpace ℂ (Fin N)))).map
        (fun z i => radial p (z i)) by
    rw [Measure.pi_map_pi (fun _ => (measurable_radial p).aemeasurable), hsph]]
  rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable, pi_ballP]
  unfold GroundTheory.Heights₂.Heights.mahler GroundTheory.Heights₂.Heights.sphereMean
  rw [average_eq', Measure.restrict_apply_univ]
  let L := (phi (k := k) B B⁻¹ h1 h2).toContinuousLinearEquiv
  have hemb : MeasurableEmbedding (phi (k := k) B B⁻¹ h1 h2) := L.toHomeomorph.measurableEmbedding
  haveI := Measure.pi.isAddHaarMeasure (fun _ : Fin k => (volume : Measure (EuclideanSpace ℂ (Fin N))))
  obtain ⟨a, ha0, ha1, hmap⟩ := exists_map_eq_smul L
    (Measure.pi fun _ : Fin k => (volume : Measure (EuclideanSpace ℂ (Fin N))))
    (volume : Measure (Fin k × Fin N → ℂ))
  have hmap' : (Measure.pi fun _ : Fin k => (volume : Measure (EuclideanSpace ℂ (Fin N)))).map
      (phi (k := k) B B⁻¹ h1 h2) = a • (volume : Measure (Fin k × Fin N → ℂ)) := hmap
  rw [← map_normalised hemb ha0 ha1 hmap', hemb.integral_map]
  have hpre : (phi (k := k) B B⁻¹ h1 h2) ⁻¹' {u | ∀ i, (h.norm fun j => u (i, j)) < 1} =
      Set.pi univ (fun _ => ball (0 : EuclideanSpace ℂ (Fin N)) 1) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
      mem_ball_zero_iff]
    exact forall_congr' (fun i => by rw [norm_phi h h1 h2 hU z i])
  rw [hpre]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ z ∂(Measure.pi fun _ : Fin k => (volume : Measure (EuclideanSpace ℂ (Fin N)))),
      ∀ i, z i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact measure_eq_zero_iff_ae_notMem.1
      (Measure.pi_eval_preimage_null (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin N))))
        (i := i) (measure_singleton 0))
  filter_upwards [Measure.ae_smul_measure (ae_restrict_of_ae hae) _] with z hz
  have harg : (fun q : Fin k × Fin N =>
      (B *ᵥ fun a => ((radial p (z q.1) : EuclideanSpace ℂ (Fin N)) a)) q.2) =
      (fun ij => ((h.norm fun j => phi (k := k) B B⁻¹ h1 h2 z (ij.1, j) : ℝ) : ℂ)⁻¹ *
        phi (k := k) B B⁻¹ h1 h2 z ij) := by
    funext q
    rw [norm_phi h h1 h2 hU z q.1, radial_coe_of_ne p (hz q.1)]
    show (B *ᵥ fun a => ((‖z q.1‖⁻¹ • z q.1 : EuclideanSpace ℂ (Fin N)) a)) q.2 =
      ((‖z q.1‖ : ℝ) : ℂ)⁻¹ * (B *ᵥ fun a => z q.1 a) q.2
    have e : (fun a => ((‖z q.1‖⁻¹ • z q.1 : EuclideanSpace ℂ (Fin N)) a)) =
        (((‖z q.1‖ : ℝ) : ℂ)⁻¹) • (fun a => z q.1 a) := by
      funext a
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_inv, ← Complex.real_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  exact congrArg (fun u => Real.log ‖MvPolynomial.eval u f‖) harg

end GlobalTheory.CompanionTheory.Ar.HS.SphereMean
