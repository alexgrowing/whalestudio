import Mathlib
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import GroundTheory.AutomorphicForms.GL2.ExistsForallAddEqOfMemFiniteSchwartzBruhat2
import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.GlobalFields.TateThesis.AdelePoisson

namespace GroundTheory.Automorphic.Adele2

open GroundTheory.Global NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure Filter
  Matrix
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap FourierTransform Real Classical
  nonZeroDivisors

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def infPart (x : Fin 2 → 𝔸[K]) : Fin 2 → mixedSpace K :=
  fun i ↦ homeomorphMixedSpace K (x i).1

def finPart (x : Fin 2 → 𝔸[K]) : Fin 2 → 𝔸ᶠ[K] :=
  fun i ↦ (x i).2

theorem infPart_neg (x : Fin 2 → 𝔸[K]) : infPart (-x) = -infPart x := by
  funext i
  simp only [infPart, Pi.neg_apply, homeomorphMixedSpace_apply]
  exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace K) (x i).1

theorem finPart_neg (x : Fin 2 → 𝔸[K]) : finPart (-x) = -finPart x := rfl

theorem infPart_algebraMap (ξ : Fin 2 → K) :
    infPart (fun i ↦ algebraMap K 𝔸[K] (ξ i)) = emb2 K ξ := by
  funext i
  simp only [infPart, emb2, adeleRing_algebraMap_fst, homeomorphMixedSpace_algebraMap]

theorem finPart_algebraMap (ξ : Fin 2 → K) :
    finPart (fun i ↦ algebraMap K 𝔸[K] (ξ i)) = fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i) := by
  funext i
  simp only [finPart, adeleRing_algebraMap_snd]

variable (K) in

def splitEquiv : (Fin 2 → 𝔸[K]) ≃ᵐ (Fin 2 → mixedSpace K) × (Fin 2 → 𝔸ᶠ[K]) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing K) 𝔸ᶠ[K] (Fin 2)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piCongrRight fun _ ↦ measurableEquivMixedSpace K)
      (MeasurableEquiv.refl _))

theorem splitEquiv_apply (x : Fin 2 → 𝔸[K]) : splitEquiv K x = (infPart x, finPart x) := rfl

theorem measurePreserving_splitEquiv :
    MeasurePreserving (splitEquiv K) (adeleMeasure2 K) ((mixedMeasure2 K).prod (finiteMeasure2 K)) :=
  (measurePreserving_arrowProdEquivProdArrow _ _ _ (fun _ ↦ infiniteAdeleMeasure K)
    (fun _ ↦ finiteAdeleMeasure K)).trans
    ((measurePreserving_pi _ _ fun _ ↦ measurePreserving_measurableEquivMixedSpace K).prod
      (MeasurePreserving.id _))

theorem adelicChar_sum_mul_eq (x y : Fin 2 → 𝔸[K]) :
    (adelicChar K (∑ i, x i * y i) : ℂ) =
      (𝐞 (-mixedPairing2 K (infPart x) (infPart y)) : ℂ) *
        (finiteAdelicChar K (∑ i, finPart x i * finPart y i) : ℂ) := by
  simp only [Fin.sum_univ_two, AddChar.map_add_eq_mul, Circle.coe_mul, adelicChar_mul_eq,
    mixedPairing2, neg_add, infPart, finPart]
  ring

def schwartzBruhatTensor2 (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) (g : (Fin 2 → 𝔸ᶠ[K]) → ℂ) :
    (Fin 2 → 𝔸[K]) → ℂ :=
  fun x ↦ φ (infPart x) * g (finPart x)

variable (K) in

def schwartzBruhat2 : Submodule ℂ ((Fin 2 → 𝔸[K]) → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : 𝓢(Fin 2 → mixedSpace K, ℂ), ∃ g ∈ finiteSchwartzBruhat2 K,
    F = schwartzBruhatTensor2 φ g}

theorem schwartzBruhatTensor2_mem (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) {g : (Fin 2 → 𝔸ᶠ[K]) → ℂ}
    (hg : g ∈ finiteSchwartzBruhat2 K) : schwartzBruhatTensor2 φ g ∈ schwartzBruhat2 K :=
  Submodule.subset_span ⟨φ, g, hg, rfl⟩

theorem schwartzBruhatTensor2_eq (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) (g : (Fin 2 → 𝔸ᶠ[K]) → ℂ) :
    schwartzBruhatTensor2 φ g = (fun p ↦ φ p.1 * g p.2) ∘ splitEquiv K := rfl

theorem integrable_schwartzBruhatTensor2 (φ : 𝓢(Fin 2 → mixedSpace K, ℂ))
    {g : (Fin 2 → 𝔸ᶠ[K]) → ℂ} (hg : g ∈ finiteSchwartzBruhat2 K) :
    Integrable (schwartzBruhatTensor2 φ g) (adeleMeasure2 K) := by
  rw [schwartzBruhatTensor2_eq, measurePreserving_splitEquiv.integrable_comp_emb
    (splitEquiv K).measurableEmbedding]
  exact (φ.integrable (μ := mixedMeasure2 K)).mul_prod (integrable_of_mem_finiteSchwartzBruhat2 hg)

theorem integrable_of_mem_schwartzBruhat2 {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K) :
    Integrable F (adeleMeasure2 K) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact integrable_schwartzBruhatTensor2 φ hg
  | zero => exact integrable_zero _ _ _
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.smul c

variable (K) in

def adelicFourier2 (F : (Fin 2 → 𝔸[K]) → ℂ) (y : Fin 2 → 𝔸[K]) : ℂ :=
  ∫ x, F x * (adelicChar K (∑ i, x i * y i) : ℂ) ∂adeleMeasure2 K

theorem continuous_adelicChar_sum_mul (y : Fin 2 → 𝔸[K]) :
    Continuous fun x : Fin 2 → 𝔸[K] ↦ (adelicChar K (∑ i, x i * y i) : ℂ) :=
  continuous_subtype_val.comp ((continuous_adelicChar (K := K)).comp
    (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const))

theorem integrable_mul_adelicChar2 {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : Integrable F (adeleMeasure2 K))
    (y : Fin 2 → 𝔸[K]) :
    Integrable (fun x ↦ F x * (adelicChar K (∑ i, x i * y i) : ℂ)) (adeleMeasure2 K) :=
  hF.mono (hF.1.mul (continuous_adelicChar_sum_mul y).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

theorem adelicFourier2_add {F G : (Fin 2 → 𝔸[K]) → ℂ} (hF : Integrable F (adeleMeasure2 K))
    (hG : Integrable G (adeleMeasure2 K)) :
    adelicFourier2 K (F + G) = adelicFourier2 K F + adelicFourier2 K G := by
  funext y
  simp only [adelicFourier2, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_adelicChar2 hF y) (integrable_mul_adelicChar2 hG y)

theorem adelicFourier2_smul (c : ℂ) (F : (Fin 2 → 𝔸[K]) → ℂ) :
    adelicFourier2 K (c • F) = c • adelicFourier2 K F := by
  funext y
  simp only [adelicFourier2, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem adelicFourier2_zero : adelicFourier2 K (0 : (Fin 2 → 𝔸[K]) → ℂ) = 0 := by
  funext y
  simp [adelicFourier2]

theorem adelicFourier2_schwartzBruhatTensor2 (φ : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (g : (Fin 2 → 𝔸ᶠ[K]) → ℂ) :
    adelicFourier2 K (schwartzBruhatTensor2 φ g) =
      schwartzBruhatTensor2 (mixedFourier2Schwartz K φ) (finiteFourier2 K g) := by
  funext y
  have h := integral_prod_mul (μ := mixedMeasure2 K) (ν := finiteMeasure2 K)
    (fun u ↦ 𝐞 (-mixedPairing2 K u (infPart y)) • φ u)
    (fun v ↦ g v * (finiteAdelicChar K (∑ i, v i * finPart y i) : ℂ))
  have e := measurePreserving_splitEquiv.integral_comp' (μ := adeleMeasure2 K)
    (f := splitEquiv K) (fun p : (Fin 2 → mixedSpace K) × (Fin 2 → 𝔸ᶠ[K]) ↦
      (𝐞 (-mixedPairing2 K p.1 (infPart y)) • φ p.1) *
        (g p.2 * (finiteAdelicChar K (∑ i, p.2 i * finPart y i) : ℂ)))
  rw [schwartzBruhatTensor2, mixedFourier2Schwartz_apply, mixedFourier2, finiteFourier2, ← h, ← e,
    adelicFourier2]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [schwartzBruhatTensor2, splitEquiv_apply, adelicChar_sum_mul_eq, Circle.smul_def,
    smul_eq_mul]
  ring

theorem adelicFourier2_mem_schwartzBruhat2 {F : (Fin 2 → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhat2 K) : adelicFourier2 K F ∈ schwartzBruhat2 K := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [adelicFourier2_schwartzBruhatTensor2]
    exact schwartzBruhatTensor2_mem _ (finiteFourier2_mem hg)
  | zero => rw [adelicFourier2_zero]; exact zero_mem _
  | add G H hG hH ihG ihH =>
    rw [adelicFourier2_add (integrable_of_mem_schwartzBruhat2 hG)
      (integrable_of_mem_schwartzBruhat2 hH)]
    exact add_mem ihG ihH
  | smul c G _ ih =>
    rw [adelicFourier2_smul]
    exact Submodule.smul_mem _ c ih

theorem adelicFourier2_adelicFourier2 {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K) :
    adelicFourier2 K (adelicFourier2 K F) = fun x ↦ F (-x) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [adelicFourier2_schwartzBruhatTensor2, adelicFourier2_schwartzBruhatTensor2,
      finiteFourier2_finiteFourier2 hg]
    funext x
    simp only [schwartzBruhatTensor2, mixedFourier2Schwartz_apply]
    rw [mixedFourier2_mixedFourier2, infPart_neg, finPart_neg]
  | zero => funext x; simp [adelicFourier2_zero]
  | add G H hG hH ihG ihH =>
    rw [adelicFourier2_add (integrable_of_mem_schwartzBruhat2 hG)
        (integrable_of_mem_schwartzBruhat2 hH),
      adelicFourier2_add (integrable_of_mem_schwartzBruhat2 (adelicFourier2_mem_schwartzBruhat2 hG))
        (integrable_of_mem_schwartzBruhat2 (adelicFourier2_mem_schwartzBruhat2 hH)), ihG, ihH]
    rfl
  | smul c G _ ih =>
    rw [adelicFourier2_smul, adelicFourier2_smul, ih]
    rfl

theorem schwartzBruhatTensor2_algebraMap (φ : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (g : (Fin 2 → 𝔸ᶠ[K]) → ℂ) (ξ : Fin 2 → K) :
    schwartzBruhatTensor2 φ g (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
      φ (emb2 K ξ) * g (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) := by
  rw [schwartzBruhatTensor2, infPart_algebraMap, finPart_algebraMap]

theorem finiteTensor2_cosetIndicator_algebraMap {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {b : Fin 2 → 𝔸ᶠ[K]} {c : Fin 2 → K}
    (hc : ∀ i, b i - algebraMap K 𝔸ᶠ[K] (c i) ∈ idealFiniteAdeles I) (ξ : Fin 2 → K) :
    finiteTensor2 (fun i ↦ cosetIndicator I (b i)) (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) =
      (coset2 K (fun _ ↦ I) c).indicator 1 ξ := by
  simp only [finiteTensor2, Fin.prod_univ_two, cosetIndicator_apply,
    algebraMap_sub_mem_idealFiniteAdeles_iff (hc 0), algebraMap_sub_mem_idealFiniteAdeles_iff (hc 1),
    Set.indicator_apply, coset2, Set.mem_ofPred_eq, Fin.forall_fin_two, Pi.one_apply]
  split_ifs <;> simp_all

theorem finiteFourier_cosetIndicator_algebraMap {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {b : 𝔸ᶠ[K]}
    {c : K} (hc : b - algebraMap K 𝔸ᶠ[K] c ∈ idealFiniteAdeles I) (η : K) :
    finiteFourier K (cosetIndicator I b) (algebraMap K 𝔸ᶠ[K] η) =
      ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ) *
        if η ∈ (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) then
          (𝐞 (mixedTraceForm K (mixedEmbedding K η) (mixedEmbedding K c)) : ℂ) else 0 := by
  rw [finiteFourier_cosetIndicator]
  by_cases hη : η ∈ (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
  · have hη' : algebraMap K 𝔸ᶠ[K] η ∈ idealFiniteAdeles (traceDualIdeal K I) :=
      (algebraMap_mem_idealFiniteAdeles_iff _ η).mpr hη
    rw [if_pos hη, Set.indicator_of_mem (SetLike.mem_coe.mpr hη'), Pi.one_apply, mul_one]
    have hb : b * algebraMap K 𝔸ᶠ[K] η = algebraMap K 𝔸ᶠ[K] c * algebraMap K 𝔸ᶠ[K] η +
        (b - algebraMap K 𝔸ᶠ[K] c) * algebraMap K 𝔸ᶠ[K] η := by ring
    rw [hb, AddChar.map_add_eq_mul, (forall_finiteAdelicChar_mul_eq_one_iff I _).mpr hη' _ hc,
      mul_one, finiteAdelicChar_algebraMap_mul, mixedTraceForm_comm K (mixedEmbedding K c)]
  · have hη' : algebraMap K 𝔸ᶠ[K] η ∉ idealFiniteAdeles (traceDualIdeal K I) :=
      fun h ↦ hη ((algebraMap_mem_idealFiniteAdeles_iff _ η).mp h)
    rw [if_neg hη, Set.indicator_of_notMem (by simpa using hη'), mul_zero, mul_zero]

theorem adelicFourier2_tensor_cosetIndicator_algebraMap (φ : 𝓢(Fin 2 → mixedSpace K, ℂ))
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {b : Fin 2 → 𝔸ᶠ[K]} {c : Fin 2 → K}
    (hc : ∀ i, b i - algebraMap K 𝔸ᶠ[K] (c i) ∈ idealFiniteAdeles I) (η : Fin 2 → K) :
    adelicFourier2 K (schwartzBruhatTensor2 φ (finiteTensor2 fun i ↦ cosetIndicator I (b i)))
        (fun i ↦ algebraMap K 𝔸[K] (η i)) =
      ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ) ^ 2 *
        (coset2 K (fun _ ↦ traceDualIdeal K I) 0).indicator
          (fun η ↦ mixedFourier2 K φ (emb2 K η) *
            (𝐞 (mixedPairing2 K (emb2 K η) (emb2 K c)) : ℂ)) η := by
  rw [adelicFourier2_schwartzBruhatTensor2, schwartzBruhatTensor2_algebraMap,
    mixedFourier2Schwartz_apply, finiteFourier2_finiteTensor2]
  simp only [finiteTensor2, Fin.prod_univ_two, finiteFourier_cosetIndicator_algebraMap (hc _),
    Set.indicator_apply, coset2, Set.mem_ofPred_eq, Fin.forall_fin_two]
  split_ifs <;> simp_all [mixedPairing2, emb2, Fin.sum_univ_two, AddChar.map_add_eq_mul]
  ring

theorem finiteAdeleMeasure_idealFiniteAdeles_sq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ) ^ 2 =
      (((∏ _i : Fin 2, ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          √|(discr K : ℝ)|))⁻¹ : ℝ) : ℂ) := by
  rw [finiteAdeleMeasure_idealFiniteAdeles_toReal, Fin.prod_univ_two, Real.coe_sqrt, coe_nnnorm,
    Int.norm_eq_abs]
  push_cast
  ring

theorem poisson_tensor_cosetIndicator (φ : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : Fin 2 → 𝔸ᶠ[K]) :
    Summable (fun ξ : Fin 2 → K ↦ ‖schwartzBruhatTensor2 φ
        (finiteTensor2 fun i ↦ cosetIndicator I (b i)) (fun i ↦ algebraMap K 𝔸[K] (ξ i))‖) ∧
      Summable (fun ξ : Fin 2 → K ↦ ‖adelicFourier2 K (schwartzBruhatTensor2 φ
        (finiteTensor2 fun i ↦ cosetIndicator I (b i))) (fun i ↦ algebraMap K 𝔸[K] (ξ i))‖) ∧
      ∑' ξ : Fin 2 → K, schwartzBruhatTensor2 φ (finiteTensor2 fun i ↦ cosetIndicator I (b i))
          (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
        ∑' ξ : Fin 2 → K, adelicFourier2 K (schwartzBruhatTensor2 φ
          (finiteTensor2 fun i ↦ cosetIndicator I (b i))) (fun i ↦ algebraMap K 𝔸[K] (ξ i)) := by
  choose c hc using fun i ↦ exists_sub_mem_idealFiniteAdeles I (b i)
  have hF : ∀ ξ : Fin 2 → K, schwartzBruhatTensor2 φ (finiteTensor2 fun i ↦ cosetIndicator I (b i))
      (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
        (coset2 K (fun _ ↦ I) c).indicator (fun ξ ↦ φ (emb2 K ξ)) ξ := by
    intro ξ
    rw [schwartzBruhatTensor2_algebraMap, finiteTensor2_cosetIndicator_algebraMap hc,
      Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp
  obtain ⟨h1, h2, h3⟩ := poisson2_coset (fun _ ↦ I) c φ
  simp only [hF, adelicFourier2_tensor_cosetIndicator_algebraMap φ hc, norm_mul]
  refine ⟨h1, h2.mul_left _, ?_⟩
  rw [tsum_mul_left, h3, finiteAdeleMeasure_idealFiniteAdeles_sq]

theorem schwartzBruhatTensor2_add (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) (g h : (Fin 2 → 𝔸ᶠ[K]) → ℂ) :
    schwartzBruhatTensor2 φ (g + h) = schwartzBruhatTensor2 φ g + schwartzBruhatTensor2 φ h := by
  funext x
  simp only [schwartzBruhatTensor2, Pi.add_apply, mul_add]

theorem schwartzBruhatTensor2_smul (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : ℂ)
    (g : (Fin 2 → 𝔸ᶠ[K]) → ℂ) :
    schwartzBruhatTensor2 φ (a • g) = a • schwartzBruhatTensor2 φ g := by
  funext x
  simp only [schwartzBruhatTensor2, Pi.smul_apply, smul_eq_mul]
  ring

theorem schwartzBruhatTensor2_zero (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) :
    schwartzBruhatTensor2 φ (0 : (Fin 2 → 𝔸ᶠ[K]) → ℂ) = 0 := by
  funext x
  simp [schwartzBruhatTensor2]

def cosetSpan2 : Submodule ℂ ((Fin 2 → 𝔸[K]) → ℂ) :=
  Submodule.span ℂ {F | ∃ (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : Fin 2 → 𝔸ᶠ[K]), F = schwartzBruhatTensor2 φ (finiteTensor2 fun i ↦ cosetIndicator I (b i))}

theorem schwartzBruhat2_eq_cosetSpan2 : schwartzBruhat2 K = cosetSpan2 (K := K) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨φ, g, hg, rfl⟩
    rw [finiteSchwartzBruhat2_eq_span] at hg
    induction hg using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨⟨I, b⟩, rfl⟩ := hh
      exact Submodule.subset_span ⟨φ, I, b, rfl⟩
    | zero => rw [schwartzBruhatTensor2_zero]; exact zero_mem _
    | add g h _ _ ihg ihh => rw [schwartzBruhatTensor2_add]; exact add_mem ihg ihh
    | smul a g _ ih => rw [schwartzBruhatTensor2_smul]; exact Submodule.smul_mem _ a ih
  · rintro _ ⟨φ, I, b, rfl⟩
    exact schwartzBruhatTensor2_mem φ (finiteTensor2_mem fun i ↦ cosetIndicator_mem_finiteSchwartzBruhat I (b i))

theorem poisson_of_mem_schwartzBruhat2 {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K) :
    Summable (fun ξ : Fin 2 → K ↦ ‖F (fun i ↦ algebraMap K 𝔸[K] (ξ i))‖) ∧
      Summable (fun ξ : Fin 2 → K ↦ ‖adelicFourier2 K F (fun i ↦ algebraMap K 𝔸[K] (ξ i))‖) ∧
      ∑' ξ : Fin 2 → K, F (fun i ↦ algebraMap K 𝔸[K] (ξ i)) =
        ∑' ξ : Fin 2 → K, adelicFourier2 K F (fun i ↦ algebraMap K 𝔸[K] (ξ i)) := by
  have hsub : cosetSpan2 (K := K) ≤ schwartzBruhat2 K := (schwartzBruhat2_eq_cosetSpan2).ge
  rw [schwartzBruhat2_eq_cosetSpan2] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact poisson_tensor_cosetIndicator φ I b
  | zero => simp [adelicFourier2_zero]
  | add G H hG hH ihG ihH =>
    rw [adelicFourier2_add (integrable_of_mem_schwartzBruhat2 (hsub hG))
      (integrable_of_mem_schwartzBruhat2 (hsub hH))]
    refine ⟨(ihG.1.add ihH.1).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ξ ↦ norm_add_le _ _,
      (ihG.2.1.add ihH.2.1).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ξ ↦ norm_add_le _ _, ?_⟩
    simp only [Pi.add_apply]
    rw [ihG.1.of_norm.tsum_add ihH.1.of_norm, ihG.2.1.of_norm.tsum_add ihH.2.1.of_norm, ihG.2.2,
      ihH.2.2]
  | smul a G hG ih =>
    rw [adelicFourier2_smul]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact ⟨ih.1.mul_left _, ih.2.1.mul_left _, by rw [tsum_mul_left, tsum_mul_left, ih.2.2]⟩

def infRingHom : 𝔸[K] →+* mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.comp (RingHom.fst _ _)

def finRingHom : 𝔸[K] →+* 𝔸ᶠ[K] := RingHom.snd _ _

theorem infPart_vecMul (x : Fin 2 → 𝔸[K]) (g : Matrix (Fin 2) (Fin 2) 𝔸[K]) :
    infPart (x ᵥ* g) = infPart x ᵥ* g.map infRingHom := by
  funext i
  exact RingHom.map_vecMul infRingHom g x i

theorem finPart_vecMul (x : Fin 2 → 𝔸[K]) (g : Matrix (Fin 2) (Fin 2) 𝔸[K]) :
    finPart (x ᵥ* g) = finPart x ᵥ* g.map finRingHom := by
  funext i
  exact RingHom.map_vecMul finRingHom g x i

def vecMulCLE (M : GL (Fin 2) (mixedSpace K)) :
    (Fin 2 → mixedSpace K) ≃L[ℝ] (Fin 2 → mixedSpace K) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ u ᵥ* (M : Matrix (Fin 2) (Fin 2) (mixedSpace K))
      invFun := fun u ↦ u ᵥ* ((M⁻¹ : GL (Fin 2) (mixedSpace K)) : Matrix (Fin 2) (Fin 2) (mixedSpace K))
      map_add' := fun u v ↦ add_vecMul _ u v
      map_smul' := fun c u ↦ smul_vecMul c u _
      left_inv := fun u ↦ by
        simp only [vecMul_vecMul, Units.mul_inv, vecMul_one]
      right_inv := fun u ↦ by
        simp only [vecMul_vecMul, Units.inv_mul, vecMul_one] }

theorem vecMulCLE_apply (M : GL (Fin 2) (mixedSpace K)) (u : Fin 2 → mixedSpace K) :
    vecMulCLE M u = u ᵥ* (M : Matrix (Fin 2) (Fin 2) (mixedSpace K)) := rfl

def rightTranslate (g : GL (Fin 2) 𝔸[K]) (F : (Fin 2 → 𝔸[K]) → ℂ) : (Fin 2 → 𝔸[K]) → ℂ :=
  fun x ↦ F (x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K]))

theorem rightTranslate_apply (g : GL (Fin 2) 𝔸[K]) (F : (Fin 2 → 𝔸[K]) → ℂ)
    (x : Fin 2 → 𝔸[K]) : rightTranslate g F x = F (x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])) := rfl

theorem rightTranslate_add (g : GL (Fin 2) 𝔸[K]) (F G : (Fin 2 → 𝔸[K]) → ℂ) :
    rightTranslate g (F + G) = rightTranslate g F + rightTranslate g G := rfl

theorem rightTranslate_smul (g : GL (Fin 2) 𝔸[K]) (a : ℂ) (F : (Fin 2 → 𝔸[K]) → ℂ) :
    rightTranslate g (a • F) = a • rightTranslate g F := rfl

theorem rightTranslate_schwartzBruhatTensor2 (g : GL (Fin 2) 𝔸[K])
    (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) (h : (Fin 2 → 𝔸ᶠ[K]) → ℂ) :
    rightTranslate g (schwartzBruhatTensor2 φ h) =
      schwartzBruhatTensor2
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (vecMulCLE (Matrix.GeneralLinearGroup.map infRingHom g)) φ)
        (fun z ↦ h (z ᵥ* ((Matrix.GeneralLinearGroup.map finRingHom g : GL (Fin 2) 𝔸ᶠ[K]) :
          Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]))) := by
  funext x
  have h1 : ((Matrix.GeneralLinearGroup.map infRingHom g : GL (Fin 2) (mixedSpace K)) :
      Matrix (Fin 2) (Fin 2) (mixedSpace K)) = (g : Matrix (Fin 2) (Fin 2) 𝔸[K]).map infRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  have h2 : ((Matrix.GeneralLinearGroup.map finRingHom g : GL (Fin 2) 𝔸ᶠ[K]) :
      Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) = (g : Matrix (Fin 2) (Fin 2) 𝔸[K]).map finRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  simp only [rightTranslate, schwartzBruhatTensor2, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, vecMulCLE_apply, h1, h2, infPart_vecMul, finPart_vecMul]

theorem rightTranslate_mem_schwartzBruhat2 (g : GL (Fin 2) 𝔸[K]) {F : (Fin 2 → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhat2 K) : rightTranslate g F ∈ schwartzBruhat2 K := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, h, hh, rfl⟩ := hG
    rw [rightTranslate_schwartzBruhatTensor2]
    exact schwartzBruhatTensor2_mem _ (comp_vecMul_mem_finiteSchwartzBruhat2 _ hh)
  | zero => exact zero_mem _
  | add G H _ _ ihG ihH => rw [rightTranslate_add]; exact add_mem ihG ihH
  | smul a G _ ih => rw [rightTranslate_smul]; exact Submodule.smul_mem _ a ih

theorem sum_vecMul_mul (x y : Fin 2 → 𝔸[K]) (A : Matrix (Fin 2) (Fin 2) 𝔸[K]) :
    ∑ i, (x ᵥ* A) i * y i = ∑ i, x i * (y ᵥ* Aᵀ) i := by
  change (x ᵥ* A) ⬝ᵥ y = x ⬝ᵥ (y ᵥ* Aᵀ)
  rw [vecMul_transpose, dotProduct_mulVec]

theorem adelicFourier2_rightTranslate (g : GL (Fin 2) 𝔸[K]) (F : (Fin 2 → 𝔸[K]) → ℂ)
    (y : Fin 2 → 𝔸[K]) :
    adelicFourier2 K (rightTranslate g F) y =
      (((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ : ℂ) *
        adelicFourier2 K F (y ᵥ* ((g⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])ᵀ) := by
  set A : Matrix (Fin 2) (Fin 2) 𝔸[K] := ((g⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])
  have h := integral_comp_vecMul g (fun z ↦ F z * (adelicChar K (∑ i, (z ᵥ* A) i * y i) : ℂ))
  have hgA : (g : Matrix (Fin 2) (Fin 2) 𝔸[K]) * A = 1 := by
    simp only [A, Units.mul_inv]
  simp only [vecMul_vecMul, hgA, vecMul_one, sum_vecMul_mul] at h
  rw [adelicFourier2, adelicFourier2]
  exact h

theorem poisson_rightTranslate {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K)
    (g : GL (Fin 2) 𝔸[K]) :
    Summable (fun ξ : Fin 2 → K ↦
        ‖F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K]))‖) ∧
      Summable (fun ξ : Fin 2 → K ↦ ‖adelicFourier2 K F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ*
        ((g⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])ᵀ)‖) ∧
      ∑' ξ : Fin 2 → K,
          F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])) =
        (((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ : ℂ) *
          ∑' ξ : Fin 2 → K, adelicFourier2 K F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ*
            ((g⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])ᵀ) := by
  obtain ⟨h1, h2, h3⟩ := poisson_of_mem_schwartzBruhat2 (rightTranslate_mem_schwartzBruhat2 g hF)
  simp only [adelicFourier2_rightTranslate, norm_mul, rightTranslate_apply] at h1 h2 h3
  have hc : ‖(((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ : ℂ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g)).2.ne')
  refine ⟨h1, (summable_mul_left_iff hc).mp h2, ?_⟩
  rw [h3, tsum_mul_left]

theorem tsum_rightTranslate_eq {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K)
    (g : GL (Fin 2) 𝔸[K]) :
    ∑' ξ : Fin 2 → K, F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])) =
      (((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ : ℂ) *
        ∑' ξ : Fin 2 → K, adelicFourier2 K F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ*
          ((g⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])ᵀ) :=
  (poisson_rightTranslate hF g).2.2

theorem continuous_infPart : Continuous (infPart (K := K)) :=
  continuous_pi fun i ↦ (homeomorphMixedSpace K).continuous.comp
    (continuous_fst.comp (continuous_apply i))

theorem continuous_finPart : Continuous (finPart (K := K)) :=
  continuous_pi fun i ↦ continuous_snd.comp (continuous_apply i)

theorem continuous_of_mem_schwartzBruhat2 {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact (φ.continuous.comp continuous_infPart).mul
      (((mem_finiteSchwartzBruhat2 K).mp hg).1.continuous.comp continuous_finPart)
  | zero => exact continuous_zero
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

theorem slice_mem_schwartzBruhat {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K) :
    (fun t : 𝔸[K] ↦ F ![0, t]) ∈ schwartzBruhat K := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    set L : mixedSpace K →L[ℝ] (Fin 2 → mixedSpace K) :=
      ContinuousLinearMap.single ℝ (fun _ : Fin 2 ↦ mixedSpace K) 1
    have hL : ∀ u, L u = Pi.single 1 u := fun u ↦ rfl
    set φ' : 𝓢(mixedSpace K, ℂ) := SchwartzMap.compCLM ℂ L.hasTemperateGrowth
      ⟨1, 1, fun u ↦ by rw [hL, Pi.norm_single, one_mul, pow_one]; linarith⟩ φ
    have hφ' : ∀ u, φ' u = φ (Pi.single 1 u) := fun u ↦ rfl
    have hcl : Topology.IsClosedEmbedding (fun v : 𝔸ᶠ[K] ↦ ![0, v]) :=
      Function.LeftInverse.isClosedEmbedding (f := fun x : Fin 2 → 𝔸ᶠ[K] ↦ x 1)
        (fun v ↦ rfl) (continuous_apply 1)
        (continuous_pi (Fin.forall_fin_two.mpr ⟨continuous_const, continuous_id⟩))
    have hg' : (fun v : 𝔸ᶠ[K] ↦ g ![0, v]) ∈ finiteSchwartzBruhat K := by
      obtain ⟨hlc, hcs⟩ := (mem_finiteSchwartzBruhat2 K).mp hg
      exact ⟨hlc.comp_continuous hcl.continuous, hcs.comp_isClosedEmbedding hcl⟩
    convert schwartzBruhatTensor_mem φ' hg' using 1
    funext t
    simp only [schwartzBruhatTensor2, schwartzBruhatTensor, hφ']
    congr 2
    · funext i
      fin_cases i
      · simp only [infPart, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [Pi.single_eq_of_ne (by decide)]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)
      · simp [infPart]
    · funext i
      fin_cases i <;> rfl
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG

end

end GroundTheory.Automorphic.Adele2
