import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureGaussian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.RealDensityCc

open GlobalTheory.GaussMean.RealDensity GlobalTheory.GaussMean.Density Filter Topology

theorem selfDual_complex_eq {ι : Type} [Fintype ι] {n : ℕ} (d : ι → Fin n → ℝ) (hd : ∀ v i, d v i ≠ 0)
    (μ : Measure (ι → Fin n → ℂ))
    (h : SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ v, ∑ i, d v i * ((x v i).re * (y v i).re + (x v i).im * (y v i).im) : ℝ) : ℂ)))) :
    μ = ENNReal.ofReal (∏ v, ∏ i, |d v i|) • (volume : Measure (ι → Fin n → ℂ)) := by
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.ReImVolume.exists_reIm_measurePreserving ι n
  have h1 := GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag (ι × Fin n × Bool) (fun k => d k.1 k.2.1) (fun k => hd _ _) _
    (selfDual_map T h fun x y => by
      congr 3
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, (hT' _ _ _).1, (hT' _ _ _).2, mul_add])
  have he : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  refine he.map_injective ?_
  rw [h1, Measure.map_smul, hT.map_eq]
  congr 2
  simp only [Fintype.prod_prod_type, Fintype.prod_bool, Real.mul_self_sqrt (abs_nonneg _)]

theorem eq_zero_of_cubes {ι : Type} [Fintype ι] {K : (ι → ℝ) → ℂ} {U : Set (ι → ℝ)} (hK : ContinuousOn K U)
    {b : ι → ℝ} (hU : U ∈ 𝓝 b)
    (h : ∀ r : ℝ, 0 < r → Set.Icc b (fun v => b v + r) ⊆ U → ∫ x in Set.Icc b (fun v => b v + r), K x = 0) :
    K b = 0 := by
  by_contra hne
  have he : 0 < ‖K b‖ := norm_pos_iff.2 hne
  have h0 : ∀ᶠ x in 𝓝 b, x ∈ U ∧ dist (K x) (K b) < ‖K b‖ / 2 :=
    (show ∀ᶠ x in 𝓝 b, x ∈ U from hU).and
      (Metric.tendsto_nhds.1 (hK.continuousAt hU) _ (half_pos he))
  obtain ⟨d, hd, hδ⟩ := Metric.eventually_nhds_iff.1 h0
  set r := d / 2 with hr
  have hr0 : 0 < r := half_pos hd
  have hin : ∀ x ∈ Set.Icc b (fun v => b v + r), dist x b < d := fun x hx => by
    refine lt_of_le_of_lt (b := r) ?_ (half_lt_self hd)
    rw [dist_pi_le_iff hr0.le]
    intro v
    have h3 := hx.1 v
    have h4 := hx.2 v
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hsub : Set.Icc b (fun v => b v + r) ⊆ U := fun x hx => (hδ (hin x hx)).1
  have hk : 0 < r ^ Fintype.card ι := pow_pos hr0 _
  have hvol : volume.real (Set.Icc b (fun v => b v + r)) = r ^ Fintype.card ι := by
    rw [Measure.real, Real.volume_Icc_pi_toReal (fun v => by simp [hr0.le])]
    simp
  have hfin : volume (Set.Icc b (fun v => b v + r)) < ⊤ := isCompact_Icc.measure_lt_top
  have h1 : ∫ x in Set.Icc b (fun v => b v + r), (K x - K b) = - ((r ^ Fintype.card ι) • K b) := by
    rw [integral_sub (hK.mono hsub).integrableOn_Icc continuousOn_const.integrableOn_Icc,
      setIntegral_const, hvol, h r hr0 hsub, zero_sub]
  have h2 : ‖∫ x in Set.Icc b (fun v => b v + r), (K x - K b)‖ ≤ ‖K b‖ / 2 * r ^ Fintype.card ι := by
    rw [← hvol]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    rw [← dist_eq_norm]
    exact (hδ (hin x hx)).2.le
  rw [h1, norm_neg, norm_smul, Real.norm_of_nonneg hk.le] at h2
  nlinarith

theorem setIntegral_box {ι : Type} [Fintype ι] {X : Type} [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (q : ι → X → ℝ) (hq : ∀ v, Measurable (q v)) (φ : ι → X → ℝ) (a c : ι → ℝ) :
    ∫ y in (fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c, ∏ v, φ v (y v) =
      ∏ v, ∫ y in q v ⁻¹' Set.Icc (a v) (c v), φ v y := by
  have hm : MeasurableSet ((fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c) :=
    measurableSet_Icc.preimage
      (measurable_pi_lambda _ fun v => (hq v).comp (measurable_pi_apply v))
  rw [← integral_indicator hm,
    ← Finset.prod_congr rfl fun v _ => integral_indicator (measurableSet_Icc.preimage (hq v)),
    ← integral_fintype_prod_volume_eq_prod]
  congr 1
  funext y
  by_cases hy : y ∈ (fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c
  · rw [Set.indicator_of_mem hy]
    exact Finset.prod_congr rfl fun v _ => (Set.indicator_of_mem (s := q v ⁻¹' Set.Icc (a v) (c v))
      ⟨hy.1 v, hy.2 v⟩ _).symm
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨v, hv⟩ : ∃ v, y v ∉ q v ⁻¹' Set.Icc (a v) (c v) := by
      by_contra! h
      exact hy ⟨fun v => (h v).1, fun v => (h v).2⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _)).symm

theorem density_eq_prod_of_isDens (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool)
    (φ : ι → (Fin n → ℂ) → ℝ) (D : ι → ℝ → ℝ) (hD : ∀ v, IsDens (ε v) (φ v) (D v)) (G : (ι → ℝ) → ℂ)
    (hG : ContinuousOn G {b | ∀ v, b v ≠ 0})
    (h : ∀ S : Set (ι → ℝ), IsCompact S → S ⊆ {b | ∀ v, b v ≠ 0} →
      ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, φ v (y v) : ℝ) : ℂ) =
        ∫ b in S, G b)
    (b : ι → ℝ) (hb : ∀ v, b v ≠ 0) : G b = ((∏ v, D v (b v) : ℝ) : ℂ) := by
  have hH : ContinuousOn (fun x : ι → ℝ => ((∏ v, D v (x v) : ℝ) : ℂ)) {b | ∀ v, b v ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_finset_prod _ fun v _ =>
      (hD v).1.comp (continuous_apply v).continuousOn fun x hx => hx v)
  have hU : {b : ι → ℝ | ∀ v, b v ≠ 0} ∈ 𝓝 b :=
    Filter.eventually_all.2 fun v => (continuous_apply v).continuousAt.eventually_ne (hb v)
  refine sub_eq_zero.1 (eq_zero_of_cubes (hG.sub hH) hU fun r hr hsub => ?_)
  simp only [Pi.sub_apply]
  rw [integral_sub (hG.mono hsub).integrableOn_Icc (hH.mono hsub).integrableOn_Icc, ← h _ isCompact_Icc hsub,
    integral_complex_ofReal, integral_complex_ofReal, sub_eq_zero,
    setIntegral_box (fun v => qEps (ε v)) (fun v => (continuous_qEps (ε v)).measurable)]
  congr 1
  refine Eq.trans ?_ (setIntegral_box (fun _ => id) (fun _ => measurable_id) D b fun v => b v + r).symm
  refine Finset.prod_congr rfl fun v _ => (hD v).2 _ isCompact_Icc fun t ht => ?_
  classical
  have := hsub (a := Function.update b v t) ⟨fun w => ?_, fun w => ?_⟩ v
  · simpa using this
  · by_cases hw : w = v
    · subst hw; simpa using ht.1
    · simp [hw]
  · by_cases hw : w = v
    · subst hw; simpa using ht.2
    · simp [hw, hr.le]

theorem density_at_sign : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ (lamv : InfinitePlace I.F → ℝ) (χ : Ainf I.F → ℂ), (∀ v, lamv v ≠ 0) → (∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) → ∀ (μi : Measure (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E)) (νi : Measure (Ainf I.F)), SelfDual μi (fun X Y => χ (BR (Ainf I.F) I.cm.sig I.J X Y)) → SelfDual νi (fun s t => χ (s * t)) → ∀ (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ) (D : InfinitePlace I.F → ℝ → ℝ), (∀ v, Continuous (φ v) ∧ HasCompactSupport (φ v) ∧ IsDens (I.ε v) (φ v) (D v)) → ∀ Fi : Ainf I.F → ℂ, IsContDensityOn μi (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) id νi {c | IsUnit c} (fun X => ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i)) : ℝ) : ℂ)) Fi → ∀ s : Bool, Fi (sgn (Ainf I.F) s) = ((∏ v, 2 ^ I.n * |lamv v| ^ ((I.n : ℝ) - 1 / 2) * D v (sgn ℝ s) : ℝ) : ℂ) := by
  intro I θ hθ lam χ hlam hχ μ ν hμ hν φ D hφ Fi hF s
  obtain ⟨a, ha⟩ := exists_coord_base I θ hθ
  obtain ⟨T, hT⟩ := exists_coord_space I θ hθ
  have hform := fun v => trace_form I v (θ v) (hθ v)
  have h2 : Module.finrank I.F I.E = 2 := I.cm.deg2
  have : FiniteDimensional I.F I.E := Module.finite_of_finrank_pos (by rw [h2]; omega)
  have : IsModuleTopology (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) := ⟨rfl⟩
  have : IsTopologicalRing (Ainf I.F ⊗[I.F] I.E) := IsModuleTopology.isTopologicalRing (Ainf I.F) _
  have : SecondCountableTopology (Ainf I.F) := a.toHomeomorph.secondCountableTopology
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := I.F) (E := I.E) (Ainf I.F)
  have : SecondCountableTopology (Ainf I.F ⊗[I.F] I.E) := e0.secondCountableTopology
  have : BorelSpace (Ainf I.F ⊗[I.F] I.E) := ⟨rfl⟩
  have : BorelSpace (Ainf I.F) := ⟨rfl⟩
  have hmul : ∀ x y v, a (x * y) v = a x v * a y v := fun x y v => by
    have : ((a (x * y) v : ℝ) : ℂ) = (a x v : ℝ) * (a y v : ℝ) := by
      rw [← ha, ← ha, ← ha, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact_mod_cast this
  have hone : ∀ v, a 1 v = 1 := fun v => by
    have : ((a 1 v : ℝ) : ℂ) = 1 := by
      rw [← ha]; exact map_one (θ v)
    exact_mod_cast this
  have hsgn : a (sgn (Ainf I.F) s) = fun _ => sgn ℝ s := by
    funext v
    cases s <;> simp [sgn, hone]
  have hhalf : ∀ v, a (algebraMap I.F (Ainf I.F) (1 / 2)) v = 1 / 2 := fun v => by
    have h1 : algebraMap I.F (Ainf I.F) (1 / 2) + algebraMap I.F (Ainf I.F) (1 / 2) = 1 := by
      rw [← map_add, add_halves, map_one]
    have := hone v
    rw [← h1, map_add, Pi.add_apply] at this
    linarith
  have htr : ∀ (X Y : Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E) v,
      a (Algebra.trace (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) (hR (Ainf I.F) I.cm.sig I.J (X 0) (Y 0))) v =
        ∑ i, (if I.ε v i then 2 else -2) * ((T X v i).re * (T Y v i).re + (T X v i).im * (T Y v i).im) :=
    fun X Y v => by
      have := hform v (X 0) (Y 0)
      rw [ha] at this
      rw [hT, hT]
      exact_mod_cast this
  have hq : ∀ X, a (qR (Ainf I.F) I.cm.sig I.J (X 0)) = fun v => qEps (I.ε v) (T X v) := fun X => by
    funext v
    rw [qR, hmul, hhalf, htr, qEps, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    split_ifs <;> ring
  have hν' := GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag _ lam hlam _ (selfDual_map a hν fun x y => by
    rw [hχ]; simp only [ha, Complex.ofReal_re, hmul])
  have hμ' := selfDual_complex_eq (fun v i => lam v * (if I.ε v i then 2 else -2))
    (fun v i => mul_ne_zero (hlam v) (by split_ifs <;> norm_num)) _ (selfDual_map T hμ fun x y => by
      rw [hχ]; simp only [ha, Complex.ofReal_re, BR, Fin.sum_univ_one, htr, Finset.mul_sum, mul_assoc])
  have hc : (∏ v, ∏ i, |lam v * (if I.ε v i then 2 else -2)|) = ∏ v, (2 * |lam v|) ^ I.n := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => 2 * |lam v|) fun i _ => by
      rw [abs_mul]; split_ifs <;> simp [mul_comm]]
    simp
  rw [hc] at hμ'
  set c : ℝ := ∏ v, (2 * |lam v|) ^ I.n with hcdef
  set c' : ℝ := ∏ v, √|lam v| with hc'def
  have hc0 : 0 < c := Finset.prod_pos fun v _ => pow_pos (mul_pos two_pos (abs_pos.2 (hlam v))) _
  have hc'0 : 0 < c' := Finset.prod_pos fun v _ => Real.sqrt_pos.2 (abs_pos.2 (hlam v))
  have heT : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hea : MeasurableEmbedding a := a.toHomeomorph.measurableEmbedding
  have hunit : ∀ x : Ainf I.F, (∀ v, a x v ≠ 0) → IsUnit x := fun x hx => by
    refine IsUnit.of_mul_eq_one (a.symm fun v => (a x v)⁻¹) (a.injective ?_)
    funext v
    rw [hmul, ContinuousAddEquiv.apply_symm_apply, hone, mul_inv_cancel₀ (hx v)]
  have key := density_eq_prod_of_isDens _ I.n I.ε φ D (fun v => (hφ v).2.2)
    (fun b => ((c' / c : ℝ) : ℂ) * Fi (a.symm b))
    (continuousOn_const.mul (hF.1.comp a.symm.continuous.continuousOn fun b hb =>
      hunit _ (by simpa using hb))) (fun S hS hSU => by
      have h1 := hF.2 (a ⁻¹' S) (a.toHomeomorph.isCompact_preimage.2 hS) fun x hx => hunit x (hSU hx)
      have h3 := hea.setIntegral_map (μ := ν) (fun b => Fi (a.symm b)) S
      have h4 := heT.setIntegral_map (μ := μ) (fun y => ((∏ v, φ v (y v) : ℝ) : ℂ))
        ((fun y v => qEps (I.ε v) (y v)) ⁻¹' S)
      simp only [ContinuousAddEquiv.symm_apply_apply] at h3
      have h5 : (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) ⁻¹' (id '' (a ⁻¹' S)) =
          T ⁻¹' ((fun y v => qEps (I.ε v) (y v)) ⁻¹' S) := by
        ext X
        simp only [Set.image_id, Set.mem_preimage, hq]
      rw [h5, ← h3] at h1
      simp only [← hT] at h1
      rw [← h4, hμ', hν', Measure.restrict_smul, Measure.restrict_smul, integral_smul_measure,
        integral_smul_measure, ENNReal.toReal_ofReal hc0.le, ENNReal.toReal_ofReal hc'0.le,
        Complex.real_smul, Complex.real_smul] at h1
      have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
      rw [integral_const_mul, Complex.ofReal_div, div_mul_eq_mul_div, ← h1, mul_div_cancel_left₀ _ hcc])
    (fun _ => sgn ℝ s) (fun _ => by cases s <;> simp [sgn])
  rw [← hsgn, ContinuousAddEquiv.symm_apply_apply] at key
  have hcc : ((c' / c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hc'0 hc0).ne'
  refine mul_left_cancel₀ hcc ?_
  rw [key, ← Complex.ofReal_mul, hcdef, hc'def, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  have hl : 0 < |lam v| := abs_pos.2 (hlam v)
  rw [Real.rpow_sub hl, Real.rpow_natCast, Real.sqrt_eq_rpow, mul_pow]
  have : 0 < |lam v| ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hl _
  field_simp

end GlobalTheory.GaussMean.RealDensityCc
