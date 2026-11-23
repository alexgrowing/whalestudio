import Mathlib
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import GroundTheory.LocalFields.LocalFourier
import GroundTheory.LocalFields.LocalFourierMult
import GroundTheory.LocalFields.LocalFourierHaar

open NumberField IsDedekindDomain MeasureTheory Filter Topology GroundTheory.Global GroundTheory.LocalField
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise

namespace GroundTheory.Automorphic.GodementSection

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

instance measurableSpace_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel _

instance borelSpace_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

def finUnitAt (v : HeightOneSpectrum (𝓞 K)) : (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v)

@[simp]
theorem coe_finUnitAt (v : HeightOneSpectrum (𝓞 K)) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((finUnitAt v b : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (b : FiniteAdeleRing (𝓞 K) K) v :=
  rfl

theorem continuous_finUnitAt (v : HeightOneSpectrum (𝓞 K)) : Continuous (finUnitAt (K := K) v) :=
  Units.continuous_map (RestrictedProduct.continuous_eval v)

theorem measurable_finUnitAt (v : HeightOneSpectrum (𝓞 K)) : Measurable (finUnitAt (K := K) v) :=
  (continuous_finUnitAt v).measurable

abbrev intUnitsAt (v : HeightOneSpectrum (𝓞 K)) : Subgroup (v.adicCompletion K)ˣ :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units

def finUnitSingle (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (IdeleGroup.finiteAdeleSingle v)

theorem finUnitAt_finUnitSingle_self (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    finUnitAt v (finUnitSingle v a) = a :=
  Units.ext (IdeleGroup.finiteAdeleSingle_apply_self v (a : v.adicCompletion K))

theorem finUnitAt_finUnitSingle_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (a : (v.adicCompletion K)ˣ) : finUnitAt w (finUnitSingle v a) = 1 :=
  Units.ext (IdeleGroup.finiteAdeleSingle_apply_of_ne h (a : v.adicCompletion K))

theorem intUnitsAt_eq_unitFiltrationUnits (v : HeightOneSpectrum (𝓞 K)) :
    intUnitsAt v = unitFiltrationUnits (v.adicCompletion K) 0 := by
  ext x
  rw [mem_unitFiltrationUnits_zero_iff, Submonoid.mem_units_iff]
  change (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ _
  rw [← mem_valuationInteger_iff, ← mem_valuationInteger_iff, Valuation.mem_integer_iff,
    Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
  have h0 : ValuativeRel.valuation (v.adicCompletion K) (x : v.adicCompletion K) ≠ 0 := by
    simp
  constructor
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    by_contra hlt
    push Not at hlt
    have := (one_lt_inv₀ (zero_lt_iff.2 h0)).2 hlt
    exact absurd h2 (not_le.2 this)
  · intro h
    simp [h]

section Units

variable (v : HeightOneSpectrum (𝓞 K))

theorem multHaar_intUnitsAt :
    multHaar (v.adicCompletion K) (intUnitsAt v : Set (v.adicCompletion K)ˣ) = 1 := by
  rw [intUnitsAt_eq_unitFiltrationUnits]
  exact multHaar_unitFiltrationUnits_zero

theorem isOpen_intUnitsAt : IsOpen (intUnitsAt v : Set (v.adicCompletion K)ˣ) :=
  IdeleGroup.isOpen_units_adicCompletionIntegers K v

theorem measurableSet_intUnitsAt : MeasurableSet (intUnitsAt v : Set (v.adicCompletion K)ˣ) :=
  (isOpen_intUnitsAt v).measurableSet

theorem finUnitAt_mem_intUnitsAt_iff (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    finUnitAt v b ∈ intUnitsAt v ↔ (b : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
      ((b⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K :=
  Iff.rfl

theorem mem_finiteIntegralUnits_iff_forall_finUnitAt (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    b ∈ finiteIntegralUnits K ↔ ∀ w : HeightOneSpectrum (𝓞 K), finUnitAt w b ∈ intUnitsAt w := by
  rw [mem_finiteIntegralUnits]
  exact forall_congr' fun w ↦ (finUnitAt_mem_intUnitsAt_iff w b).symm

end Units

section AtS

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def finUnitsAt : (FiniteAdeleRing (𝓞 K) K)ˣ →* ((v : S) → (v.1.adicCompletion K)ˣ) :=
  MonoidHom.pi fun v ↦ finUnitAt v.1

@[simp]
theorem finUnitsAt_apply (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : S) :
    finUnitsAt S b v = finUnitAt v.1 b :=
  rfl

theorem continuous_finUnitsAt : Continuous (finUnitsAt (K := K) S) :=
  continuous_pi fun v ↦ continuous_finUnitAt v.1

theorem measurable_finUnitsAt : Measurable (finUnitsAt (K := K) S) :=
  (continuous_finUnitsAt S).measurable

def finUnitsSingle : ((v : S) → (v.1.adicCompletion K)ˣ) →* (FiniteAdeleRing (𝓞 K) K)ˣ where
  toFun a := ∏ v : S, finUnitSingle v.1 (a v)
  map_one' := by simp
  map_mul' a a' := by
    simp only [Pi.mul_apply, map_mul]
    exact Finset.prod_mul_distrib

theorem finUnitAt_finUnitsSingle_of_mem (a : (v : S) → (v.1.adicCompletion K)ˣ) (w : S) :
    finUnitAt w.1 (finUnitsSingle S a) = a w := by
  classical
  change finUnitAt w.1 (∏ v : S, finUnitSingle v.1 (a v)) = a w
  rw [map_prod, Finset.prod_eq_single w]
  · exact finUnitAt_finUnitSingle_self w.1 (a w)
  · intro u _ hu
    exact finUnitAt_finUnitSingle_of_ne (fun h ↦ hu (Subtype.ext h).symm) _
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem finUnitAt_finUnitsSingle_of_notMem (a : (v : S) → (v.1.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ S) : finUnitAt w (finUnitsSingle S a) = 1 := by
  change finUnitAt w (∏ v : S, finUnitSingle v.1 (a v)) = 1
  rw [map_prod]
  refine Finset.prod_eq_one fun u _ ↦ finUnitAt_finUnitSingle_of_ne (fun h ↦ hw (by rw [h]; exact u.2)) _

theorem finUnitsAt_finUnitsSingle_mul (a : (v : S) → (v.1.adicCompletion K)ˣ)
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : finUnitsAt S (finUnitsSingle S a * b) = a * finUnitsAt S b := by
  funext w
  simp only [map_mul, Pi.mul_apply, finUnitsAt_apply, finUnitAt_finUnitsSingle_of_mem]

theorem apply_finUnitsSingle_mul {E : Type*} {G : (FiniteAdeleRing (𝓞 K) K)ˣ → E}
    (hG : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → G b = G b')
    (a : (v : S) → (v.1.adicCompletion K)ˣ) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    G (finUnitsSingle S a * b) = G b :=
  hG _ _ fun w hw ↦ by rw [map_mul, finUnitAt_finUnitsSingle_of_notMem S a hw, one_mul]

def intUnitsAtS : Set ((v : S) → (v.1.adicCompletion K)ˣ) :=
  Set.univ.pi fun v ↦ (intUnitsAt v.1 : Set (v.1.adicCompletion K)ˣ)

theorem isOpen_intUnitsAtS : IsOpen (intUnitsAtS (K := K) S) :=
  isOpen_set_pi Set.finite_univ fun v _ ↦ isOpen_intUnitsAt v.1

theorem measurableSet_intUnitsAtS : MeasurableSet (intUnitsAtS (K := K) S) :=
  (isOpen_intUnitsAtS S).measurableSet

abbrev multHaarS : Measure ((v : S) → (v.1.adicCompletion K)ˣ) :=
  Measure.pi fun v ↦ multHaar (v.1.adicCompletion K)

theorem multHaarS_intUnitsAtS : multHaarS (K := K) S (intUnitsAtS S) = 1 := by
  rw [intUnitsAtS, Measure.pi_pi]
  exact Finset.prod_eq_one fun v _ ↦ multHaar_intUnitsAt v.1

def awayImageS (g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) : Measure ((v : S) → (v.1.adicCompletion K)ˣ) :=
  Measure.map (finUnitsAt S) ((finiteIdeleMeasure K).withDensity g)

variable {S}

theorem awayImageS_apply (g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    {A : Set ((v : S) → (v.1.adicCompletion K)ˣ)} (hA : MeasurableSet A) :
    awayImageS S g A = ∫⁻ b, (finUnitsAt S ⁻¹' A).indicator g b ∂finiteIdeleMeasure K := by
  rw [awayImageS, Measure.map_apply (measurable_finUnitsAt S) hA,
    withDensity_apply _ (measurable_finUnitsAt S hA), lintegral_indicator (measurable_finUnitsAt S hA)]

theorem isMulLeftInvariant_awayImageS {g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞}
    (hinv : ∀ a b, g (finUnitsSingle S a * b) = g b) : (awayImageS S g).IsMulLeftInvariant := by
  constructor
  intro a
  ext A hA
  rw [Measure.map_apply (measurable_const_mul a) hA, awayImageS_apply g (measurable_const_mul a hA),
    awayImageS_apply g hA, ← lintegral_mul_left_eq_self _ (finUnitsSingle S a⁻¹)]
  congr 1
  funext b
  have h : finUnitsAt S (finUnitsSingle S a⁻¹ * b) = a⁻¹ * finUnitsAt S b :=
    finUnitsAt_finUnitsSingle_mul S a⁻¹ b
  classical
  simp only [Set.indicator_apply, Set.mem_preimage, h, mul_inv_cancel_left, hinv]

theorem isFiniteMeasureOnCompacts_awayImageS {g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞}
    (hinv : ∀ a b, g (finUnitsSingle S a * b) = g b) (hc : awayImageS S g (intUnitsAtS S) ≠ ∞) :
    IsFiniteMeasureOnCompacts (awayImageS S g) := by
  have := isMulLeftInvariant_awayImageS hinv
  refine ⟨fun C hC ↦ ?_⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun a : C ↦ (a : (v : S) → (v.1.adicCompletion K)ˣ) • intUnitsAtS S)
    (fun a ↦ (isOpen_intUnitsAtS S).smul _)
    (fun c hc ↦ Set.mem_iUnion.2 ⟨⟨c, hc⟩, Set.mem_smul_set.2
      ⟨1, fun v _ ↦ one_mem (intUnitsAt v.1), mul_one c⟩⟩)
  calc awayImageS S g C
      ≤ awayImageS S g (⋃ i ∈ t, (i : (v : S) → (v.1.adicCompletion K)ˣ) • intUnitsAtS S) :=
        measure_mono ht
    _ ≤ ∑ i ∈ t, awayImageS S g ((i : (v : S) → (v.1.adicCompletion K)ˣ) • intUnitsAtS S) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _i ∈ t, awayImageS S g (intUnitsAtS S) :=
        Finset.sum_congr rfl fun i _ ↦ measure_smul _ _ _
    _ < ∞ := ENNReal.sum_lt_top.2 fun _ _ ↦ hc.lt_top

theorem awayImageS_eq_smul {g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞}
    (hinv : ∀ a b, g (finUnitsSingle S a * b) = g b) (hc : awayImageS S g (intUnitsAtS S) ≠ ∞) :
    awayImageS S g = awayImageS S g (intUnitsAtS S) • multHaarS S := by
  have := isMulLeftInvariant_awayImageS hinv
  have := isFiniteMeasureOnCompacts_awayImageS hinv hc
  have h := Measure.isMulLeftInvariant_eq_smul (awayImageS S g) (multHaarS S)
  set c := Measure.haarScalarFactor (awayImageS S g) (multHaarS S)
  have hU : awayImageS S g (intUnitsAtS S) = (c : ℝ≥0∞) := by
    conv_lhs => rw [h]
    rw [Measure.smul_apply, multHaarS_intUnitsAtS, ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [hU]
  conv_lhs => rw [h]
  ext A _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

end AtS

section Integrals

variable {S : Finset (HeightOneSpectrum (𝓞 K))}

theorem integral_comp_finUnitsAt_mul_nnreal {g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0}
    (hg : Measurable g) (hinv : ∀ a b, g (finUnitsSingle S a * b) = g b)
    (hgi : Integrable ((finUnitsAt S ⁻¹' intUnitsAtS S).indicator fun b ↦ (g b : ℝ))
      (finiteIdeleMeasure K))
    {F : ((v : S) → (v.1.adicCompletion K)ˣ) → ℂ} (hF : Integrable F (multHaarS S)) :
    Integrable (fun b ↦ F (finUnitsAt S b) * ((g b : ℝ) : ℂ)) (finiteIdeleMeasure K) ∧
      ∫ b, F (finUnitsAt S b) * ((g b : ℝ) : ℂ) ∂finiteIdeleMeasure K =
        (∫ a, F a ∂multHaarS S) *
          ((∫ b, (finUnitsAt S ⁻¹' intUnitsAtS S).indicator (fun b ↦ (g b : ℝ)) b
            ∂finiteIdeleMeasure K : ℝ) : ℂ) := by
  set gE : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun b ↦ (g b : ℝ≥0∞) with hgE
  set I : ℝ := ∫ b, (finUnitsAt S ⁻¹' intUnitsAtS S).indicator (fun b ↦ (g b : ℝ)) b
    ∂finiteIdeleMeasure K with hI
  have hinvE : ∀ a b, gE (finUnitsSingle S a * b) = gE b := fun a b ↦ by simp only [hgE, hinv]
  have hcI : awayImageS S gE (intUnitsAtS S) = ENNReal.ofReal I := by
    rw [awayImageS_apply gE (measurableSet_intUnitsAtS S), hI,
      ofReal_integral_eq_lintegral_ofReal hgi
        (Eventually.of_forall fun b ↦ Set.indicator_nonneg (fun b _ ↦ (g b).2) b)]
    congr 1
    funext b
    classical
    simp only [Set.indicator_apply, hgE]
    split_ifs
    · exact (ENNReal.ofReal_coe_nnreal).symm
    · exact ENNReal.ofReal_zero.symm
  have hc : awayImageS S gE (intUnitsAtS S) ≠ ∞ := by rw [hcI]; exact ENNReal.ofReal_ne_top
  have e := awayImageS_eq_smul hinvE hc
  rw [hcI] at e
  have hmap : Measure.map (finUnitsAt S) ((finiteIdeleMeasure K).withDensity gE) =
      ENNReal.ofReal I • multHaarS S := e
  have hFm : AEStronglyMeasurable F
      (Measure.map (finUnitsAt S) ((finiteIdeleMeasure K).withDensity gE)) := by
    rw [hmap]
    exact hF.aestronglyMeasurable.smul_measure _
  have hpt : ∀ b, F (finUnitsAt S b) * ((g b : ℝ) : ℂ) = g b • F (finUnitsAt S b) := fun b ↦ by
    rw [NNReal.smul_def, Complex.real_smul, mul_comm]
  simp_rw [hpt]
  constructor
  · rw [← integrable_withDensity_iff_integrable_smul hg]
    have : Integrable F (Measure.map (finUnitsAt S) ((finiteIdeleMeasure K).withDensity gE)) := by
      rw [hmap]
      exact hF.smul_measure ENNReal.ofReal_ne_top
    exact (integrable_map_measure hFm (measurable_finUnitsAt S).aemeasurable).1 this
  · rw [← integral_withDensity_eq_integral_smul hg,
      ← integral_map (measurable_finUnitsAt S).aemeasurable hFm, hmap, integral_smul_measure,
      ENNReal.toReal_ofReal (hI ▸ integral_nonneg fun b ↦ Set.indicator_nonneg (fun b _ ↦ (g b).2) b),
      Complex.real_smul, mul_comm]

theorem integral_finiteIdele_local_mul {F : ((v : S) → (v.1.adicCompletion K)ˣ) → ℂ}
    (hF : Integrable F (multHaarS S)) {G : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ} (hGm : Measurable G)
    (hG : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → G b = G b')
    (hGi : Integrable ((finUnitsAt S ⁻¹' intUnitsAtS S).indicator G) (finiteIdeleMeasure K)) :
    Integrable (fun b ↦ F (finUnitsAt S b) * G b) (finiteIdeleMeasure K) ∧
      ∫ b, F (finUnitsAt S b) * G b ∂finiteIdeleMeasure K =
        (∫ a, F a ∂multHaarS S) *
          ∫ b, (finUnitsAt S ⁻¹' intUnitsAtS S).indicator G b ∂finiteIdeleMeasure K := by
  set U := finUnitsAt S ⁻¹' intUnitsAtS S with hUdef
  have hUm : MeasurableSet U := measurable_finUnitsAt S (measurableSet_intUnitsAtS S)
  have key : ∀ p : ℂ → ℝ, Measurable p → (∀ z, |p z| ≤ ‖z‖) →
      Integrable (U.indicator fun b ↦ (((p (G b)).toNNReal : ℝ))) (finiteIdeleMeasure K) ∧
      Integrable (fun b ↦ F (finUnitsAt S b) * (((p (G b)).toNNReal : ℝ) : ℂ)) (finiteIdeleMeasure K) ∧
      ∫ b, F (finUnitsAt S b) * (((p (G b)).toNNReal : ℝ) : ℂ) ∂finiteIdeleMeasure K =
        (∫ a, F a ∂multHaarS S) *
          ((∫ b, U.indicator (fun b ↦ (((p (G b)).toNNReal : ℝ))) b ∂finiteIdeleMeasure K : ℝ) : ℂ) := by
    intro p hp hpz
    have hgm : Measurable fun b ↦ (p (G b)).toNNReal := (hp.comp hGm).real_toNNReal
    have hinv : ∀ a b, (p (G (finUnitsSingle S a * b))).toNNReal = (p (G b)).toNNReal :=
      fun a b ↦ by rw [apply_finUnitsSingle_mul S hG a b]
    have hgi : Integrable (U.indicator fun b ↦ (((p (G b)).toNNReal : ℝ))) (finiteIdeleMeasure K) := by
      refine hGi.norm.mono' ((measurable_coe_nnreal_real.comp hgm).indicator hUm).aestronglyMeasurable
        (Eventually.of_forall fun b ↦ ?_)
      classical
      simp only [Set.indicator_apply]
      split_ifs
      · rw [Real.norm_of_nonneg (NNReal.coe_nonneg _), Real.coe_toNNReal']
        exact max_le ((le_abs_self _).trans (hpz _)) (norm_nonneg _)
      · simp
    obtain ⟨h1, h2⟩ := integral_comp_finUnitsAt_mul_nnreal hgm hinv hgi hF
    exact ⟨hgi, h1, h2⟩
  obtain ⟨i1, j1, e1⟩ := key (fun z ↦ z.re) Complex.measurable_re fun z ↦ Complex.abs_re_le_norm z
  obtain ⟨i2, j2, e2⟩ := key (fun z ↦ -z.re) Complex.measurable_re.neg fun z ↦ by
    rw [abs_neg]; exact Complex.abs_re_le_norm z
  obtain ⟨i3, j3, e3⟩ := key (fun z ↦ z.im) Complex.measurable_im fun z ↦ Complex.abs_im_le_norm z
  obtain ⟨i4, j4, e4⟩ := key (fun z ↦ -z.im) Complex.measurable_im.neg fun z ↦ by
    rw [abs_neg]; exact Complex.abs_im_le_norm z
  have hsplit : ∀ z : ℂ, z = ((((z.re).toNNReal : ℝ) - ((-z.re).toNNReal : ℝ) : ℝ) : ℂ) +
      ((((z.im).toNNReal : ℝ) - ((-z.im).toNNReal : ℝ) : ℝ) : ℂ) * Complex.I := fun z ↦ by
    simp only [Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]
    exact (Complex.re_add_im z).symm
  have hL : ∀ b, F (finUnitsAt S b) * G b =
      (F (finUnitsAt S b) * ((((G b).re).toNNReal : ℝ) : ℂ) -
        F (finUnitsAt S b) * (((-(G b).re).toNNReal : ℝ) : ℂ)) +
      (F (finUnitsAt S b) * ((((G b).im).toNNReal : ℝ) : ℂ) -
        F (finUnitsAt S b) * (((-(G b).im).toNNReal : ℝ) : ℂ)) * Complex.I := fun b ↦ by
    conv_lhs => rw [hsplit (G b)]
    push_cast
    ring
  have hR : ∀ b, U.indicator G b =
      (((U.indicator (fun b ↦ (((G b).re).toNNReal : ℝ)) b -
        U.indicator (fun b ↦ ((-(G b).re).toNNReal : ℝ)) b : ℝ) : ℂ)) +
      (((U.indicator (fun b ↦ (((G b).im).toNNReal : ℝ)) b -
        U.indicator (fun b ↦ ((-(G b).im).toNNReal : ℝ)) b : ℝ) : ℂ)) * Complex.I := fun b ↦ by
    classical
    simp only [Set.indicator_apply]
    split_ifs
    · exact hsplit (G b)
    · simp
  set f1 := fun b ↦ F (finUnitsAt S b) * ((((G b).re).toNNReal : ℝ) : ℂ)
  set f2 := fun b ↦ F (finUnitsAt S b) * (((-(G b).re).toNNReal : ℝ) : ℂ)
  set f3 := fun b ↦ F (finUnitsAt S b) * ((((G b).im).toNNReal : ℝ) : ℂ)
  set f4 := fun b ↦ F (finUnitsAt S b) * (((-(G b).im).toNNReal : ℝ) : ℂ)
  set r1 := U.indicator (fun b ↦ (((G b).re).toNNReal : ℝ))
  set r2 := U.indicator (fun b ↦ ((-(G b).re).toNNReal : ℝ))
  set r3 := U.indicator (fun b ↦ (((G b).im).toNNReal : ℝ))
  set r4 := U.indicator (fun b ↦ ((-(G b).im).toNNReal : ℝ))
  have k12 : Integrable (fun b ↦ f1 b - f2 b) (finiteIdeleMeasure K) := j1.sub j2
  have k34 : Integrable (fun b ↦ (f3 b - f4 b) * Complex.I) (finiteIdeleMeasure K) :=
    (j3.sub j4).mul_const _
  have l12 : Integrable (fun b ↦ ((r1 b - r2 b : ℝ) : ℂ)) (finiteIdeleMeasure K) := (i1.sub i2).ofReal
  have l34 : Integrable (fun b ↦ ((r3 b - r4 b : ℝ) : ℂ) * Complex.I) (finiteIdeleMeasure K) :=
    (i3.sub i4).ofReal.mul_const _
  have hL' : (fun b ↦ F (finUnitsAt S b) * G b) = fun b ↦ (f1 b - f2 b) + (f3 b - f4 b) * Complex.I :=
    funext hL
  have hR' : U.indicator G = fun b ↦ ((r1 b - r2 b : ℝ) : ℂ) + ((r3 b - r4 b : ℝ) : ℂ) * Complex.I :=
    funext hR
  refine ⟨?_, ?_⟩
  · rw [hL']
    exact k12.add k34
  · rw [hL', hR', integral_add k12 k34, integral_add l12 l34, integral_sub j1 j2, integral_mul_const,
      integral_sub j3 j4, e1, e2, e3, e4, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_sub i1 i2, integral_sub i3 i4]
    push_cast
    ring

theorem integral_finiteIdele_prod_local_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Fv : ∀ v : S, (v.1.adicCompletion K)ˣ → ℂ)
    (hFv : ∀ v, Integrable (Fv v) (multHaar (v.1.adicCompletion K)))
    {G : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ} (hGm : Measurable G)
    (hG : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → G b = G b')
    (hGi : Integrable ((finUnitsAt S ⁻¹' intUnitsAtS S).indicator G) (finiteIdeleMeasure K)) :
    Integrable (fun b ↦ (∏ v : S, Fv v (finUnitAt v.1 b)) * G b) (finiteIdeleMeasure K) ∧
      ∫ b, (∏ v : S, Fv v (finUnitAt v.1 b)) * G b ∂finiteIdeleMeasure K =
        (∏ v : S, ∫ a, Fv v a ∂multHaar (v.1.adicCompletion K)) *
          ∫ b, (finUnitsAt S ⁻¹' intUnitsAtS S).indicator G b ∂finiteIdeleMeasure K := by
  have hF : Integrable (fun a : (v : S) → (v.1.adicCompletion K)ˣ ↦ ∏ v : S, Fv v (a v))
      (multHaarS S) := Integrable.fintype_prod_dep hFv
  have h := integral_finiteIdele_local_mul hF hGm hG hGi
  rw [integral_fintype_prod_eq_prod] at h
  exact h

end Integrals

end

end GroundTheory.Automorphic.GodementSection
