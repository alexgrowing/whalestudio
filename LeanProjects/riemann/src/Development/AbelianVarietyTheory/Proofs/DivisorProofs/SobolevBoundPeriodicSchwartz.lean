import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzContinuousHasDerivAtArchimedeanLinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitCubeTranslatesSlabPeriodicLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabOpenUnitCubeHaarPosFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabCoveredByTranslatesOfSmallerSlabStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntervalIntegralLeMulIntervalIntegralSq
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem schA_line (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t :=
  GlobalTheory.T.adelicSchwartz_continuous_hasDerivAt_archimedeanLine F κ

theorem slice_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G) (π : G →+ (Fin N → ℝ))
    (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) (U : Set G)
    (hU : MeasurableSet {w | w - ι (π w) ∈ U})
    (hfin : ∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hper : ∀ w, ∀ u ∈ U, φ (w + u) = φ w) (y : G) :
    μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ :=
  GlobalTheory.T.lintegral_unitCube_translates_slabPeriodic_le μ ι π hι hπ hπι U hU hfin φ hφ hper y

theorem slab_top (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧
        ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ :=
  GlobalTheory.T.archimedeanSlab_open_unitCube_haar_pos_finite F κ

theorem slab_cover (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ c : ℕ, ∀ m : ℕ, 0 < m → slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧
      (∀ r ∈ R, arch F r = 0) ∧ ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m :=
  GlobalTheory.T.archimedeanSlab_covered_by_translates_of_smaller_slab F κ

end GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem wordD_cons (v : κ → mixedEmbedding.mixedSpace F) (w : List (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → AF F) → ℂ) : wordD F (v :: w) f = dD F v (wordD F w f) := rfl

theorem per_dD {m : ℕ} {f : (κ → AF F) → ℂ} (h : Per F m f) (v : κ → mixedEmbedding.mixedSpace F) :
    Per F m (dD F v f) := by
  intro x z hz
  unfold dD
  congr 1
  funext t
  rw [add_right_comm]
  exact h _ z hz

theorem per_wordD {m : ℕ} {f : (κ → AF F) → ℂ} (h : Per F m f) (w : List (κ → mixedEmbedding.mixedSpace F)) :
    Per F m (wordD F w f) := by
  induction w with
  | nil => exact h
  | cons v w ih => rw [wordD_cons]; exact per_dD ih v

theorem wordD_mem {f : (κ → AF F) → ℂ} (hf : f ∈ schA F κ) (w : List (κ → mixedEmbedding.mixedSpace F)) :
    wordD F w f ∈ schA F κ := by
  induction w with
  | nil => exact hf
  | cons v w ih => rw [wordD_cons]; exact GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F κ (Sum.inl v) _ ih

theorem archIn_single (j : Fin (dimA F κ)) (s : ℝ) :
    archIn F κ (Pi.single j s) = fun i => infAd F (s • ubasis F κ j i) := by
  funext i
  rw [archIn_apply]
  congr 1
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_eq_single j (fun c hc => by simp [Pi.single_apply, hc])]
  simp

theorem sobolev_schA {f : (κ → AF F) → ℂ} (hf : f ∈ schA F κ) (x : κ → AF F) (B : ℝ)
    (hB : ∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ dimA F κ → (∀ v ∈ w, ∃ j, v = ubasis F κ j) →
      ∫ t in cube (dimA F κ), ‖wordD F w f (x + archIn F κ t)‖ ^ 2 ≤ B) :
    ‖f x‖ ^ 2 ≤ 4 ^ dimA F κ * B := by
  let A : ℕ → Set ((κ → AF F) → ℂ) := fun p =>
    {u | ∃ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ p ∧ (∀ v ∈ w, ∃ j, v = ubasis F κ j) ∧
      u = wordD F w f}
  have hA : Monotone A := fun p q hpq u ⟨w, h1, h2, h3⟩ => ⟨w, h1.trans hpq, h2, h3⟩
  have key := GlobalTheory.ThetaGrowth.sobolev_iter (dimA F κ) 0 (fun j s => archIn F κ (Pi.single j s)) A B x
    (fun j => (continuous_archIn F κ).comp (continuous_single (A := fun _ : Fin (dimA F κ) => ℝ) j)) hA ?_ ?_ f ⟨[], by simp, by simp, rfl⟩
  · exact key
  · rintro p u ⟨w, h1, h2, rfl⟩
    have hmem := wordD_mem hf w
    refine ⟨(schA_line F κ _ hmem).1, fun j => ⟨wordD F (ubasis F κ j :: w) f,
      ⟨_, by simpa using h1, ?_, rfl⟩, fun y => ?_⟩⟩
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨j, rfl⟩
      · exact h2 v hv
    · have hd := (schA_line F κ _ hmem).2 (ubasis F κ j) y
      have hc : Continuous fun s : ℝ => y + fun i => infAd F (s • ubasis F κ j i) :=
        continuous_const.add (continuous_pi fun i => (continuous_infAd F).comp (continuous_id.smul continuous_const))
      have := GlobalTheory.sobolev_endpoint_one_variable ℂ (fun s => wordD F w f (y + fun i => infAd F (s • ubasis F κ j i)))
        (fun s => dD F (ubasis F κ j) (wordD F w f) (y + fun i => infAd F (s • ubasis F κ j i))) 1 one_pos
        (fun t _ => hd t)
        (((schA_line F κ _ (wordD_mem hf (ubasis F κ j :: w))).1.comp hc).continuousOn)
      simp only [archIn_single, wordD_cons]
      simpa [infAd_zero, ← Pi.zero_def] using this
  · rintro u ⟨w, h1, h2, rfl⟩
    have e : ∀ t : Fin (dimA F κ) → ℝ, ∑ j, archIn F κ (Pi.single j (t j)) = archIn F κ t := by
      intro t
      rw [← map_sum, Finset.univ_sum_single]
    simp only [e]
    exact hB w (by simpa using h1) h2

end GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem cube_bound (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ φ : (κ → AF F) → ℂ, Continuous φ → Per F m φ → ∀ b : ℝ, 0 ≤ b →
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b → ∀ y,
        ∫ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨hopen, hμ1⟩ := slab_top F κ
  obtain ⟨h0, hfin1⟩ := hμ1 μ hμ
  obtain ⟨c, hc⟩ := slab_cover F κ
  have hQc : IsCompact (cube (dimA F κ)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hc₁ : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ≠ ⊤ := hfin1 _ hQc
  refine ⟨(μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal⁻¹, c, by positivity,
    fun m hm φ hφ hper b hb hL y => ?_⟩
  obtain ⟨hsub, R, hRc, hR0, hRcov⟩ := hc m hm
  have hcm : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ≤
      (m : ℝ≥0∞) ^ c * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by
    calc μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)
        ≤ ∑ r ∈ R, μ ((fun w => r + w) '' (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m)) := by
          refine (measure_mono ?_).trans (measure_biUnion_finset_le R _)
          rintro w ⟨hwQ, hw1⟩
          obtain ⟨r, hr, hwr⟩ := hRcov w hw1
          have hπr : archOut F κ r = 0 := by rw [archOut_apply, hR0 r hr, map_zero]
          refine Set.mem_biUnion hr ⟨w - r, ⟨?_, hwr⟩, by abel_nf⟩
          show archOut F κ (w - r) ∈ cube (dimA F κ)
          rw [map_sub, hπr, sub_zero]; exact hwQ
      _ = ∑ r ∈ R, μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Set.image_add_left, measure_preimage_add]
      _ = R.card * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr; exact_mod_cast hRc
  have hS := slice_le μ (archIn F κ) (archOut F κ) (continuous_archIn F κ) (continuous_archOut F κ)
    (archOut_archIn F κ) (perSet F κ m) (hopen m hm).measurableSet
    (fun A hA => ne_top_of_le_ne_top (hfin1 A hA) (measure_mono (Set.inter_subset_inter_right _ hsub)))
    (fun w => ‖φ w‖ₑ ^ 2) (hφ.measurable.enorm.pow_const 2)
    (fun w u hu => by simp only [hper w u hu]) y
  set X := ∫⁻ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ₑ ^ 2
  have h1 : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) * X ≤ (m : ℝ≥0∞) ^ c * ENNReal.ofReal b :=
    calc _ ≤ (m : ℝ≥0∞) ^ c * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) * X := by gcongr
      _ = (m : ℝ≥0∞) ^ c * (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) * X) := by ring
      _ ≤ _ := by gcongr; exact hS.trans hL
  have hI : ∫ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ ^ 2 = X.toReal := by
    have hcont : Continuous fun t => ‖φ (y + archIn F κ t)‖ ^ 2 :=
      (hφ.comp (continuous_const.add (continuous_archIn F κ))).norm.pow 2
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (y + archIn F κ t)‖ ^ 2)
      (ae_of_all _ fun _ => by positivity) hcont.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h2 : (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal * X.toReal ≤ (m : ℝ) ^ c * b := by
    rw [← ENNReal.toReal_mul]
    refine (ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) h1).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hb]
  have hpos : 0 < (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal := ENNReal.toReal_pos h0.ne' hc₁
  rw [hI, mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hpos, mul_comm]
  exact h2

theorem sobolev_per : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ,
      Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) →
        ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  intro F _ _ κ _ μ hμ
  obtain ⟨C₀, c, -, hb⟩ := cube_bound μ hμ
  refine ⟨dimA F κ, 4 ^ dimA F κ * C₀, c, fun m hm f hf hper b hb0 hw x => ?_⟩
  have := sobolev_schA hf x (C₀ * m ^ c * b) fun w hl hv =>
    hb m hm _ (schA_line F κ _ (wordD_mem hf w)).1 (per_wordD hper w) b hb0
      (hw w hl fun v hv' => by obtain ⟨j, rfl⟩ := hv v hv'; rw [norm_ubasis]) x
  calc _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.ArchDecay

example : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ, Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) → ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := GlobalTheory.ArchDecay.sobolev_per
