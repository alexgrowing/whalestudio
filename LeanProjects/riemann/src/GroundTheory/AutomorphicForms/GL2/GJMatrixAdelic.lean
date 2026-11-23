import Mathlib
import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
import GroundTheory.AutomorphicForms.GL2.GJMatrixFinite
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite

namespace GroundTheory.Automorphic.GJMatrix

open GroundTheory.Global NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
  Filter
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap FourierTransform Real Classical
  nonZeroDivisors

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

variable (K) in

def adeleMeasurePi : Measure (ι → 𝔸[K]) := Measure.pi fun _ ↦ adeleMeasure K

instance : (adeleMeasurePi K (ι := ι)).IsAddHaarMeasure := by
  unfold adeleMeasurePi; infer_instance

instance : SigmaFinite (adeleMeasurePi K (ι := ι)) := by
  unfold adeleMeasurePi; infer_instance

def infPartPi (x : ι → 𝔸[K]) : ι → mixedSpace K :=
  fun i ↦ homeomorphMixedSpace K (x i).1

def finPartPi (x : ι → 𝔸[K]) : ι → 𝔸ᶠ[K] :=
  fun i ↦ (x i).2

omit [Fintype ι] in
theorem infPartPi_neg (x : ι → 𝔸[K]) : infPartPi (-x) = -infPartPi x := by
  funext i
  simp only [infPartPi, Pi.neg_apply, homeomorphMixedSpace_apply]
  exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace K) (x i).1

omit [Fintype ι] in
theorem finPartPi_neg (x : ι → 𝔸[K]) : finPartPi (-x) = -finPartPi x := rfl

omit [Fintype ι] in
theorem infPartPi_algebraMap (ξ : ι → K) :
    infPartPi (fun i ↦ algebraMap K 𝔸[K] (ξ i)) = embPi K ξ := by
  funext i
  simp only [infPartPi, embPi, adeleRing_algebraMap_fst, homeomorphMixedSpace_algebraMap]

omit [Fintype ι] in
theorem finPartPi_algebraMap (ξ : ι → K) :
    finPartPi (fun i ↦ algebraMap K 𝔸[K] (ξ i)) = fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i) := by
  funext i
  simp only [finPartPi, adeleRing_algebraMap_snd]

variable (K ι) in

def splitEquivPi : (ι → 𝔸[K]) ≃ᵐ (ι → mixedSpace K) × (ι → 𝔸ᶠ[K]) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing K) 𝔸ᶠ[K] ι).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piCongrRight fun _ ↦ measurableEquivMixedSpace K)
      (MeasurableEquiv.refl _))

omit [Fintype ι] in
theorem splitEquivPi_apply (x : ι → 𝔸[K]) : splitEquivPi K ι x = (infPartPi x, finPartPi x) := rfl

theorem measurePreserving_splitEquivPi :
    MeasurePreserving (splitEquivPi K ι) (adeleMeasurePi K)
      ((mixedMeasurePi K).prod (finiteMeasurePi K)) :=
  (measurePreserving_arrowProdEquivProdArrow _ _ _ (fun _ ↦ infiniteAdeleMeasure K)
    (fun _ ↦ finiteAdeleMeasure K)).trans
    ((measurePreserving_pi _ _ fun _ ↦ measurePreserving_measurableEquivMixedSpace K).prod
      (MeasurePreserving.id _))

theorem adelicChar_sum_mul_eq_pi (x y : ι → 𝔸[K]) :
    (adelicChar K (∑ i, x i * y i) : ℂ) =
      (𝐞 (-mixedPairingPi K (infPartPi x) (infPartPi y)) : ℂ) *
        (finiteAdelicChar K (∑ i, finPartPi x i * finPartPi y i) : ℂ) := by
  rw [addChar_sum, mixedPairingPi, ← Finset.sum_neg_distrib, addChar_sum (𝐞),
    addChar_sum (finiteAdelicChar K), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [adelicChar_mul_eq]
  rfl

def schwartzBruhatTensorPi (φ : 𝓢(ι → mixedSpace K, ℂ)) (g : (ι → 𝔸ᶠ[K]) → ℂ) :
    (ι → 𝔸[K]) → ℂ :=
  fun x ↦ φ (infPartPi x) * g (finPartPi x)

variable (K ι) in

def schwartzBruhatPi : Submodule ℂ ((ι → 𝔸[K]) → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : 𝓢(ι → mixedSpace K, ℂ), ∃ g ∈ finiteSchwartzBruhatPi K,
    F = schwartzBruhatTensorPi φ g}

theorem schwartzBruhatTensorPi_mem (φ : 𝓢(ι → mixedSpace K, ℂ)) {g : (ι → 𝔸ᶠ[K]) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi K) : schwartzBruhatTensorPi φ g ∈ schwartzBruhatPi K ι :=
  Submodule.subset_span ⟨φ, g, hg, rfl⟩

theorem schwartzBruhatTensorPi_eq (φ : 𝓢(ι → mixedSpace K, ℂ)) (g : (ι → 𝔸ᶠ[K]) → ℂ) :
    schwartzBruhatTensorPi φ g = (fun p ↦ φ p.1 * g p.2) ∘ splitEquivPi K ι := rfl

theorem integrable_schwartzBruhatTensorPi (φ : 𝓢(ι → mixedSpace K, ℂ))
    {g : (ι → 𝔸ᶠ[K]) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi K) :
    Integrable (schwartzBruhatTensorPi φ g) (adeleMeasurePi K) := by
  rw [schwartzBruhatTensorPi_eq, measurePreserving_splitEquivPi.integrable_comp_emb
    (splitEquivPi K ι).measurableEmbedding]
  exact (φ.integrable (μ := mixedMeasurePi K)).mul_prod
    (integrable_of_mem_finiteSchwartzBruhatPi hg)

theorem integrable_of_mem_schwartzBruhatPi {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K ι) :
    Integrable F (adeleMeasurePi K) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact integrable_schwartzBruhatTensorPi φ hg
  | zero => exact integrable_zero _ _ _
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.smul c

omit [Fintype ι] in
theorem continuous_infPartPi : Continuous (infPartPi (K := K) (ι := ι)) :=
  continuous_pi fun i ↦ (homeomorphMixedSpace K).continuous.comp
    (continuous_fst.comp (continuous_apply i))

omit [Fintype ι] in
theorem continuous_finPartPi : Continuous (finPartPi (K := K) (ι := ι)) :=
  continuous_pi fun i ↦ continuous_snd.comp (continuous_apply i)

theorem continuous_of_mem_schwartzBruhatPi {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K ι) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact (φ.continuous.comp continuous_infPartPi).mul
      (((mem_finiteSchwartzBruhatPi K).mp hg).1.continuous.comp continuous_finPartPi)
  | zero => exact continuous_zero
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

variable (K) in

def adelicFourierPi (F : (ι → 𝔸[K]) → ℂ) (y : ι → 𝔸[K]) : ℂ :=
  ∫ x, F x * (adelicChar K (∑ i, x i * y i) : ℂ) ∂adeleMeasurePi K

theorem continuous_adelicChar_sum_mul_pi (y : ι → 𝔸[K]) :
    Continuous fun x : ι → 𝔸[K] ↦ (adelicChar K (∑ i, x i * y i) : ℂ) :=
  continuous_subtype_val.comp ((continuous_adelicChar (K := K)).comp
    (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const))

theorem integrable_mul_adelicChar_pi {F : (ι → 𝔸[K]) → ℂ} (hF : Integrable F (adeleMeasurePi K))
    (y : ι → 𝔸[K]) :
    Integrable (fun x ↦ F x * (adelicChar K (∑ i, x i * y i) : ℂ)) (adeleMeasurePi K) :=
  hF.mono (hF.1.mul (continuous_adelicChar_sum_mul_pi y).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

theorem adelicFourierPi_add {F G : (ι → 𝔸[K]) → ℂ} (hF : Integrable F (adeleMeasurePi K))
    (hG : Integrable G (adeleMeasurePi K)) :
    adelicFourierPi K (F + G) = adelicFourierPi K F + adelicFourierPi K G := by
  funext y
  simp only [adelicFourierPi, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_adelicChar_pi hF y) (integrable_mul_adelicChar_pi hG y)

theorem adelicFourierPi_smul (c : ℂ) (F : (ι → 𝔸[K]) → ℂ) :
    adelicFourierPi K (c • F) = c • adelicFourierPi K F := by
  funext y
  simp only [adelicFourierPi, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem adelicFourierPi_zero : adelicFourierPi K (0 : (ι → 𝔸[K]) → ℂ) = 0 := by
  funext y
  simp [adelicFourierPi]

theorem adelicFourierPi_schwartzBruhatTensorPi (φ : 𝓢(ι → mixedSpace K, ℂ))
    (g : (ι → 𝔸ᶠ[K]) → ℂ) :
    adelicFourierPi K (schwartzBruhatTensorPi φ g) =
      schwartzBruhatTensorPi (mixedFourierPiSchwartz K φ) (finiteFourierPi K g) := by
  funext y
  have h := integral_prod_mul (μ := mixedMeasurePi K) (ν := finiteMeasurePi K)
    (fun u ↦ 𝐞 (-mixedPairingPi K u (infPartPi y)) • φ u)
    (fun v ↦ g v * (finiteAdelicChar K (∑ i, v i * finPartPi y i) : ℂ))
  have e := measurePreserving_splitEquivPi.integral_comp' (μ := adeleMeasurePi K)
    (f := splitEquivPi K ι) (fun p : (ι → mixedSpace K) × (ι → 𝔸ᶠ[K]) ↦
      (𝐞 (-mixedPairingPi K p.1 (infPartPi y)) • φ p.1) *
        (g p.2 * (finiteAdelicChar K (∑ i, p.2 i * finPartPi y i) : ℂ)))
  rw [schwartzBruhatTensorPi, mixedFourierPiSchwartz_apply, mixedFourierPi, finiteFourierPi, ← h,
    ← e, adelicFourierPi]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [schwartzBruhatTensorPi, splitEquivPi_apply, adelicChar_sum_mul_eq_pi, Circle.smul_def,
    smul_eq_mul]
  ring

theorem adelicFourierPi_mem_schwartzBruhatPi {F : (ι → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi K ι) : adelicFourierPi K F ∈ schwartzBruhatPi K ι := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [adelicFourierPi_schwartzBruhatTensorPi]
    exact schwartzBruhatTensorPi_mem _ (finiteFourierPi_mem hg)
  | zero => rw [adelicFourierPi_zero]; exact zero_mem _
  | add G H hG hH ihG ihH =>
    rw [adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi hG)
      (integrable_of_mem_schwartzBruhatPi hH)]
    exact add_mem ihG ihH
  | smul c G _ ih =>
    rw [adelicFourierPi_smul]
    exact Submodule.smul_mem _ c ih

theorem adelicFourierPi_adelicFourierPi {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K ι) :
    adelicFourierPi K (adelicFourierPi K F) = fun x ↦ F (-x) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [adelicFourierPi_schwartzBruhatTensorPi, adelicFourierPi_schwartzBruhatTensorPi,
      finiteFourierPi_finiteFourierPi hg]
    funext x
    simp only [schwartzBruhatTensorPi, mixedFourierPiSchwartz_apply]
    rw [mixedFourierPi_mixedFourierPi, infPartPi_neg, finPartPi_neg]
  | zero => funext x; simp [adelicFourierPi_zero]
  | add G H hG hH ihG ihH =>
    rw [adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi hG)
        (integrable_of_mem_schwartzBruhatPi hH),
      adelicFourierPi_add
        (integrable_of_mem_schwartzBruhatPi (adelicFourierPi_mem_schwartzBruhatPi hG))
        (integrable_of_mem_schwartzBruhatPi (adelicFourierPi_mem_schwartzBruhatPi hH)), ihG, ihH]
    rfl
  | smul c G _ ih =>
    rw [adelicFourierPi_smul, adelicFourierPi_smul, ih]
    rfl

theorem schwartzBruhatTensorPi_algebraMap (φ : 𝓢(ι → mixedSpace K, ℂ))
    (g : (ι → 𝔸ᶠ[K]) → ℂ) (ξ : ι → K) :
    schwartzBruhatTensorPi φ g (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
      φ (embPi K ξ) * g (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) := by
  rw [schwartzBruhatTensorPi, infPartPi_algebraMap, finPartPi_algebraMap]

theorem finiteTensor_cosetIndicator_algebraMap {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {b : ι → 𝔸ᶠ[K]} {c : ι → K}
    (hc : ∀ i, b i - algebraMap K 𝔸ᶠ[K] (c i) ∈ idealFiniteAdeles J) (ξ : ι → K) :
    finiteTensor (fun i ↦ cosetIndicator J (b i)) (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) =
      (cosetPi K (fun _ ↦ J) c).indicator 1 ξ := by
  simp only [finiteTensor, cosetIndicator_apply, fun i ↦ algebraMap_sub_mem_idealFiniteAdeles_iff
    (hc i), Finset.prod_boole, Finset.mem_univ, true_implies, Set.indicator_apply, cosetPi,
    Set.mem_ofPred_eq, Pi.one_apply]

theorem adelicFourierPi_tensor_cosetIndicator_algebraMap (φ : 𝓢(ι → mixedSpace K, ℂ))
    {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {b : ι → 𝔸ᶠ[K]} {c : ι → K}
    (hc : ∀ i, b i - algebraMap K 𝔸ᶠ[K] (c i) ∈ idealFiniteAdeles J) (η : ι → K) :
    adelicFourierPi K (schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator J (b i)))
        (fun i ↦ algebraMap K 𝔸[K] (η i)) =
      ((finiteAdeleMeasure K (idealFiniteAdeles J)).toReal : ℂ) ^ Fintype.card ι *
        (cosetPi K (fun _ ↦ traceDualIdeal K J) 0).indicator
          (fun η ↦ mixedFourierPi K φ (embPi K η) *
            (𝐞 (mixedPairingPi K (embPi K η) (embPi K c)) : ℂ)) η := by
  rw [adelicFourierPi_schwartzBruhatTensorPi, schwartzBruhatTensorPi_algebraMap,
    mixedFourierPiSchwartz_apply, finiteFourierPi_finiteTensor]
  simp only [finiteTensor, Adele2.finiteFourier_cosetIndicator_algebraMap (hc _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  by_cases hη : ∀ i, η i ∈ (traceDualIdeal K J : FractionalIdeal (𝓞 K)⁰ K)
  · have hmem : η ∈ cosetPi K (fun _ ↦ traceDualIdeal K J) 0 := fun i ↦ by simpa using hη i
    rw [Set.indicator_of_mem hmem]
    simp only [if_pos (hη _)]
    simp only [mixedPairingPi, embPi]
    rw [addChar_sum Real.fourierChar Finset.univ]
    ring
  · have hmem : η ∉ cosetPi K (fun _ ↦ traceDualIdeal K J) 0 := fun h ↦ hη fun i ↦ by
      simpa using h i
    obtain ⟨i, hi⟩ := not_forall.mp hη
    rw [Set.indicator_of_notMem hmem, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
    ring

theorem finiteAdeleMeasure_idealFiniteAdeles_pow (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((finiteAdeleMeasure K (idealFiniteAdeles J)).toReal : ℂ) ^ Fintype.card ι =
      (((∏ _i : ι, ((FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          √|(discr K : ℝ)|))⁻¹ : ℝ) : ℂ) := by
  rw [finiteAdeleMeasure_idealFiniteAdeles_toReal, Finset.prod_const, Finset.card_univ,
    Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  push_cast
  rw [← mul_inv, inv_pow]

theorem poissonPi_tensor_cosetIndicator (φ : 𝓢(ι → mixedSpace K, ℂ))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K]) :
    Summable (fun ξ : ι → K ↦ ‖schwartzBruhatTensorPi φ
        (finiteTensor fun i ↦ cosetIndicator J (b i)) (fun i ↦ algebraMap K 𝔸[K] (ξ i))‖) ∧
      Summable (fun ξ : ι → K ↦ ‖adelicFourierPi K (schwartzBruhatTensorPi φ
        (finiteTensor fun i ↦ cosetIndicator J (b i))) (fun i ↦ algebraMap K 𝔸[K] (ξ i))‖) ∧
      ∑' ξ : ι → K, schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator J (b i))
          (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
        ∑' ξ : ι → K, adelicFourierPi K (schwartzBruhatTensorPi φ
          (finiteTensor fun i ↦ cosetIndicator J (b i))) (fun i ↦ algebraMap K 𝔸[K] (ξ i)) := by
  choose c hc using fun i ↦ exists_sub_mem_idealFiniteAdeles J (b i)
  have hF : ∀ ξ : ι → K, schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator J (b i))
      (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
        (cosetPi K (fun _ ↦ J) c).indicator (fun ξ ↦ φ (embPi K ξ)) ξ := by
    intro ξ
    rw [schwartzBruhatTensorPi_algebraMap, finiteTensor_cosetIndicator_algebraMap hc,
      Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp
  obtain ⟨h1, h2, h3⟩ := poissonPi_coset (fun _ ↦ J) c φ
  simp only [hF, adelicFourierPi_tensor_cosetIndicator_algebraMap φ hc, norm_mul]
  refine ⟨h1, h2.mul_left _, ?_⟩
  rw [tsum_mul_left, h3, finiteAdeleMeasure_idealFiniteAdeles_pow]

theorem schwartzBruhatTensorPi_add (φ : 𝓢(ι → mixedSpace K, ℂ)) (g h : (ι → 𝔸ᶠ[K]) → ℂ) :
    schwartzBruhatTensorPi φ (g + h) = schwartzBruhatTensorPi φ g + schwartzBruhatTensorPi φ h := by
  funext x
  simp only [schwartzBruhatTensorPi, Pi.add_apply, mul_add]

theorem schwartzBruhatTensorPi_smul (φ : 𝓢(ι → mixedSpace K, ℂ)) (a : ℂ)
    (g : (ι → 𝔸ᶠ[K]) → ℂ) :
    schwartzBruhatTensorPi φ (a • g) = a • schwartzBruhatTensorPi φ g := by
  funext x
  simp only [schwartzBruhatTensorPi, Pi.smul_apply, smul_eq_mul]
  ring

theorem schwartzBruhatTensorPi_zero (φ : 𝓢(ι → mixedSpace K, ℂ)) :
    schwartzBruhatTensorPi φ (0 : (ι → 𝔸ᶠ[K]) → ℂ) = 0 := by
  funext x
  simp [schwartzBruhatTensorPi]

variable (K ι) in

def cosetSpanPi : Submodule ℂ ((ι → 𝔸[K]) → ℂ) :=
  Submodule.span ℂ {F | ∃ (φ : 𝓢(ι → mixedSpace K, ℂ)) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : ι → 𝔸ᶠ[K]), F = schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator J (b i))}

theorem schwartzBruhatPi_eq_cosetSpanPi : schwartzBruhatPi K ι = cosetSpanPi K ι := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨φ, g, hg, rfl⟩
    rw [finiteSchwartzBruhatPi_eq_span] at hg
    induction hg using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨⟨J, b⟩, rfl⟩ := hh
      exact Submodule.subset_span ⟨φ, J, b, rfl⟩
    | zero => rw [schwartzBruhatTensorPi_zero]; exact zero_mem _
    | add g h _ _ ihg ihh => rw [schwartzBruhatTensorPi_add]; exact add_mem ihg ihh
    | smul a g _ ih => rw [schwartzBruhatTensorPi_smul]; exact Submodule.smul_mem _ a ih
  · rintro _ ⟨φ, J, b, rfl⟩
    exact schwartzBruhatTensorPi_mem φ
      (finiteTensor_mem fun i ↦ cosetIndicator_mem_finiteSchwartzBruhat J (b i))

theorem poisson_of_mem_schwartzBruhatPi {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K ι) :
    Summable (fun ξ : ι → K ↦ ‖F (fun i ↦ algebraMap K 𝔸[K] (ξ i))‖) ∧
      Summable (fun ξ : ι → K ↦ ‖adelicFourierPi K F (fun i ↦ algebraMap K 𝔸[K] (ξ i))‖) ∧
      ∑' ξ : ι → K, F (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
        ∑' ξ : ι → K, adelicFourierPi K F (fun i ↦ algebraMap K 𝔸[K] (ξ i)) := by
  have hsub : cosetSpanPi K ι ≤ schwartzBruhatPi K ι := schwartzBruhatPi_eq_cosetSpanPi.ge
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, J, b, rfl⟩ := hG
    exact poissonPi_tensor_cosetIndicator φ J b
  | zero => simp [adelicFourierPi_zero]
  | add G H hG hH ihG ihH =>
    rw [adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi (hsub hG))
      (integrable_of_mem_schwartzBruhatPi (hsub hH))]
    refine ⟨(ihG.1.add ihH.1).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ξ ↦ norm_add_le _ _,
      (ihG.2.1.add ihH.2.1).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ξ ↦ norm_add_le _ _, ?_⟩
    simp only [Pi.add_apply]
    rw [ihG.1.of_norm.tsum_add ihH.1.of_norm, ihG.2.1.of_norm.tsum_add ihH.2.1.of_norm, ihG.2.2,
      ihH.2.2]
  | smul a G hG ih =>
    rw [adelicFourierPi_smul]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact ⟨ih.1.mul_left _, ih.2.1.mul_left _, by rw [tsum_mul_left, tsum_mul_left, ih.2.2]⟩

theorem tsum_algebraMap_eq_tsum_adelicFourierPi {F : (ι → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi K ι) :
    ∑' ξ : ι → K, F (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
      ∑' ξ : ι → K, adelicFourierPi K F (fun i ↦ algebraMap K 𝔸[K] (ξ i)) :=
  (poisson_of_mem_schwartzBruhatPi hF).2.2

end

end GroundTheory.Automorphic.GJMatrix
