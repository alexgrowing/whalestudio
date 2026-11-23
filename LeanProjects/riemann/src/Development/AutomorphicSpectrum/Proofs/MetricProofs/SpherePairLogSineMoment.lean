import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo

noncomputable section

def crd (m : S2) : Fin 3 → ℝ := fun i => (m : E3) i

def dens (a : ℂ) : ℝ := Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2

def stereoMeasure : Measure ℂ := volume.withDensity fun a => ENNReal.ofReal (dens a)

theorem continuous_crd : Continuous crd :=
  continuous_pi fun i => (EuclideanSpace.proj i).continuous.comp continuous_subtype_val

theorem measurable_dens : Measurable dens := by
  have : Continuous dens := by
    unfold dens
    refine continuous_const.div (by fun_prop) fun a => ?_
    positivity
  exact this.measurable

theorem dens_nonneg (a : ℂ) : 0 ≤ dens a := by
  unfold dens
  have := Real.pi_pos
  positivity

theorem measurable_nS : Measurable nS := by
  have : Continuous nS := by
    refine continuous_pi fun i => ?_
    unfold nS
    refine Continuous.div ?_ (by fun_prop) fun a => by positivity
    fin_cases i <;> simp <;> fun_prop
  exact this.measurable

theorem stereo_hyp (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) :
    (Integrable (fun a : ℂ => f (nS a) * dens a) ↔ Integrable (fun m : S2 => f (crd m)) sphereMeasure) ∧
      ∫ a : ℂ, f (nS a) * dens a = ∫ m : S2, f (crd m) ∂sphereMeasure :=
  (GlobalTheory.T.sphere_measure_stereographic_integral).1 f hf

theorem map_stereo : stereoMeasure.map nS = sphereMeasure.map crd := by
  have := FibreLocal.isProbabilityMeasure_sphere
  ext s hs
  rw [Measure.map_apply measurable_nS hs, Measure.map_apply continuous_crd.measurable hs]
  have hpre := continuous_crd.measurable hs
  have hpre' := measurable_nS hs
  have hf : Measurable (s.indicator (1 : (Fin 3 → ℝ) → ℝ)) := measurable_one.indicator hs
  have hfI : Integrable (fun m : S2 => s.indicator (1 : (Fin 3 → ℝ) → ℝ) (crd m)) sphereMeasure :=
    (integrable_const (1 : ℝ)).indicator hpre
  obtain ⟨h1, h2⟩ := stereo_hyp _ hf
  have hI := h1.2 hfI
  have hnn : 0 ≤ᵐ[volume] fun a => s.indicator (1 : (Fin 3 → ℝ) → ℝ) (nS a) * dens a :=
    Eventually.of_forall fun a => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (dens_nonneg a)
  calc stereoMeasure (nS ⁻¹' s) = ∫⁻ a in nS ⁻¹' s, ENNReal.ofReal (dens a) := withDensity_apply _ hpre'
    _ = ∫⁻ a, ENNReal.ofReal (s.indicator (1 : (Fin 3 → ℝ) → ℝ) (nS a) * dens a) := by
        rw [← lintegral_indicator hpre']
        refine lintegral_congr fun a => ?_
        by_cases ha : nS a ∈ s
        · simp [Set.indicator, ha]
        · simp [Set.indicator, ha]
    _ = ENNReal.ofReal (∫ a, s.indicator (1 : (Fin 3 → ℝ) → ℝ) (nS a) * dens a) :=
        (ofReal_integral_eq_lintegral_ofReal hI hnn).symm
    _ = ENNReal.ofReal (∫ m, s.indicator (1 : (Fin 3 → ℝ) → ℝ) (crd m) ∂sphereMeasure) := by rw [h2]
    _ = sphereMeasure (crd ⁻¹' s) := by
        have h3 : ∫ m, s.indicator (1 : (Fin 3 → ℝ) → ℝ) (crd m) ∂sphereMeasure =
            sphereMeasure.real (crd ⁻¹' s) := integral_indicator_one hpre
        rw [h3]
        exact ofReal_measureReal

instance : IsFiniteMeasure stereoMeasure := by
  have := FibreLocal.isProbabilityMeasure_sphere
  constructor
  have h := congrArg (fun μ => μ Set.univ) map_stereo
  simp only [Measure.map_apply measurable_nS MeasurableSet.univ,
    Measure.map_apply continuous_crd.measurable MeasurableSet.univ, Set.preimage_univ] at h
  rw [h]
  simp

theorem integral_pair (Φ : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ) (hΦ : Measurable Φ) :
    ∫ p : ℂ × ℂ, dens p.1 * dens p.2 * Φ (nS p.1, nS p.2) =
      ∫ p : S2 × S2, Φ (crd p.1, crd p.2) ∂(sphereMeasure.prod sphereMeasure) := by
  have := FibreLocal.isProbabilityMeasure_sphere
  have hc := continuous_crd.measurable
  have hn := measurable_nS
  have hmap : (stereoMeasure.prod stereoMeasure).map (Prod.map nS nS) =
      (sphereMeasure.prod sphereMeasure).map (Prod.map crd crd) := by
    rw [← Measure.map_prod_map _ _ hn hn, ← Measure.map_prod_map _ _ hc hc, map_stereo]
  have hd : Measurable fun a => ENNReal.ofReal (dens a) := ENNReal.measurable_ofReal.comp measurable_dens
  have hprod : stereoMeasure.prod stereoMeasure =
      (volume : Measure (ℂ × ℂ)).withDensity
        (fun p => ENNReal.ofReal (dens p.1) * ENNReal.ofReal (dens p.2)) := by
    rw [stereoMeasure, prod_withDensity hd hd]
    rfl
  have hL : ∫ p : ℂ × ℂ, dens p.1 * dens p.2 * Φ (nS p.1, nS p.2) =
      ∫ p, Φ (Prod.map nS nS p) ∂(stereoMeasure.prod stereoMeasure) := by
    rw [hprod, integral_withDensity_eq_integral_toReal_smul₀
      (by exact ((hd.comp measurable_fst).mul (hd.comp measurable_snd)).aemeasurable)
      (Eventually.of_forall fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (dens_nonneg _),
      ENNReal.toReal_ofReal (dens_nonneg _)]
    rfl
  rw [hL, ← integral_map (hn.prodMap hn).aemeasurable hΦ.aestronglyMeasurable, hmap,
    integral_map (hc.prodMap hc).aemeasurable hΦ.aestronglyMeasurable]
  rfl

def dp {Ω : Type*} (u : Ω → Fin 3 → ℝ) : MvPolynomial (Fin 3) (Ω → ℝ) :=
  ∑ i, X i * C (fun q => u q i)

def pp {Ω : Type*} (u v : Ω → Fin 3 → ℝ) (Q : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) (Ω → ℝ) :=
  aeval ![dp u, dp v] Q

theorem map_pp {Ω : Type*} (u v : Ω → Fin 3 → ℝ) (Q : MvPolynomial (Fin 2) ℝ) (p : Ω) :
    map (Pi.evalRingHom (fun _ : Ω => ℝ) p) (pp u v Q) = aeval ![lin3 (u p), lin3 (v p)] Q := by
  have h : map (Pi.evalRingHom (fun _ : Ω => ℝ) p) (pp u v Q) =
      mapAlgHom (Pi.evalAlgHom ℝ (fun _ : Ω => ℝ) p) (pp u v Q) := rfl
  rw [h, pp, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext r
  fin_cases r
  · simp [dp, lin3, mapAlgHom_apply]
  · simp [dp, lin3, mapAlgHom_apply]

theorem ell_eq (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (R : MvPolynomial (Fin 3) ℝ)
    (S : Finset (Fin 3 →₀ ℕ)) (hS : R.support ⊆ S) :
    ℓ R = ∑ m ∈ S, coeff m R * ℓ (monomial m 1) := by
  conv_lhs => rw [R.as_sum]
  rw [map_sum]
  rw [← Finset.sum_subset hS fun m _ hm => by simp [notMem_support_iff.1 hm]]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_one (coeff m R), ← smul_eq_mul, ← smul_monomial, map_smul, smul_eq_mul, smul_eq_mul, mul_one]

theorem ell_pp {Ω : Type*} (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (u v : Ω → Fin 3 → ℝ)
    (Q : MvPolynomial (Fin 2) ℝ) (p : Ω) :
    ℓ (aeval ![lin3 (u p), lin3 (v p)] Q) =
      ∑ m ∈ (pp u v Q).support, coeff m (pp u v Q) p * ℓ (monomial m 1) := by
  rw [← map_pp, ell_eq ℓ _ _ (support_map_subset _ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map]
  rfl

theorem continuous_coeff_pp {Ω : Type*} [TopologicalSpace Ω] (u v : Ω → Fin 3 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (Q : MvPolynomial (Fin 2) ℝ) (m : Fin 3 →₀ ℕ) :
    Continuous (coeff m (pp u v Q)) := by
  set φ : C(Ω, ℝ) →ₐ[ℝ] (Ω → ℝ) := ContinuousMap.coeFnAlgHom (α := Ω) (A := ℝ) ℝ
  set w : Fin 2 → MvPolynomial (Fin 3) C(Ω, ℝ) :=
    ![∑ i, X i * C ⟨fun q => u q i, (continuous_apply i).comp hu⟩,
      ∑ i, X i * C ⟨fun q => v q i, (continuous_apply i).comp hv⟩]
  have hw : ![dp u, dp v] = fun r => mapAlgHom φ (w r) := by
    funext r
    fin_cases r
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, w, dp, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]
      rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, w, dp, mapAlgHom_apply, map_sum,
        map_mul, map_X, map_C]
      rfl
  rw [pp, hw, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
  exact (coeff m (aeval w Q)).continuous

theorem continuous_ell (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => ℓ (aeval ![lin3 p.1, lin3 p.2] Q) := by
  have h := ell_pp ℓ (Prod.fst : (Fin 3 → ℝ) × (Fin 3 → ℝ) → _) Prod.snd Q
  simp only [h]
  exact continuous_finset_sum _ fun m _ =>
    (continuous_coeff_pp _ _ continuous_fst continuous_snd Q m).mul continuous_const

def ker (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ := (1 / 2) * Real.log ((1 - ∑ i, p.1 i * p.2 i) / 2)

theorem measurable_ker : Measurable ker := by
  have hc : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (1 - ∑ i, p.1 i * p.2 i) / 2 := by fun_prop
  exact (Real.measurable_log.comp hc.measurable).const_mul (1 / 2)

theorem ker_crd (p : S2 × S2) : ker (crd p.1, crd p.2) = wwLogWeight p := by
  have h : ∑ i, crd p.1 i * crd p.2 i = inner ℝ (p.1 : E3) (p.2 : E3) := by
    simp [crd, PiLp.inner_apply, mul_comm]
  simp only [ker, wwLogWeight, h]

theorem pp_eq (Q : MvPolynomial (Fin 2) ℝ) :
    pp (fun p : S2 × S2 => crd p.1) (fun p => crd p.2) Q =
      aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q := rfl

theorem ell_moment (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ) :
    ℓ (momentPoly (sphereMeasure.prod sphereMeasure) wwLogWeight
        (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) =
      ∫ p : S2 × S2, wwLogWeight p * ℓ (aeval ![lin3 (crd p.1), lin3 (crd p.2)] Q)
        ∂(sphereMeasure.prod sphereMeasure) := by
  have hI : ∀ m, Integrable (fun p => wwLogWeight p *
      coeff m (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q) p)
      (sphereMeasure.prod sphereMeasure) := fun m =>
    FibreLocal.integrable_mul _ (DiagFibreMoment.continuous_coeff_aeval Q m)
  have h := fun p : S2 × S2 => ell_pp ℓ (fun p : S2 × S2 => crd p.1) (fun p => crd p.2) Q p
  simp only [pp_eq] at h
  simp only [h, Finset.mul_sum]
  rw [integral_finset_sum _ fun m _ => by
    simpa only [mul_assoc] using (hI m).mul_const (ℓ (monomial m 1))]
  rw [momentPoly, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [← mul_assoc]
  rw [integral_mul_const, ← mul_one (∫ p, _ ∂_), ← smul_eq_mul, ← smul_monomial, map_smul, smul_eq_mul,
    smul_eq_mul, mul_one]

theorem integral_eq_moment : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ),
    ∫ p : ℂ × ℂ, logSin 1 p.1 p.2 * (wS p.1 * wS p.2 * ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)] Q)) =
      Real.pi ^ 2 * ℓ (momentPoly (sphereMeasure.prod sphereMeasure) wwLogWeight
        (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  intro ℓ Q
  have hΦ : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ker p * ℓ (aeval ![lin3 p.1, lin3 p.2] Q) := measurable_ker.mul (continuous_ell ℓ Q).measurable
  have h := integral_pair _ hΦ
  rw [ell_moment]
  simp only [ker_crd] at h
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hk : logSin 1 p.1 p.2 = ker (nS p.1, nS p.2) := (GlobalTheory.T.sphere_measure_stereographic_integral).2 p.1 p.2
  have hw : ∀ a, wS a = Real.pi * dens a := fun a => by
    have := Real.pi_ne_zero
    simp only [wS, dens]
    field_simp
  simp only [hk, hw]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo
