import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureFubiniLocallyCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAutomorphismMeasureScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImaginaryLineMeasureScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateLeviConjugationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditiveAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinateHomeomorphStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.UnipConj.aeFacts (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalRing (AE F E) ∧ LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) ∧ T2Space (AE F E) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact ⟨inferInstance, e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, e.isEmbedding.t2Space⟩

theorem GlobalTheory.UnipConj.lintegral_conj_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (μN : Measure (unip σ G.V H)), μN.IsHaarMeasure →
    ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h →
    ∀ f : UA σ G.V.J → ℝ≥0∞, Measurable f →
      ∫⁻ n, f (h * n.1 * h⁻¹) ∂μN = ((absE F E l : ℝ≥0∞) ^ (b + 1))⁻¹ * ∫⁻ n, f n.1 ∂μN := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ μN hμ l g₀ h hL f hf
  obtain ⟨iR, iLC, iSC, iT2⟩ := GlobalTheory.UnipConj.aeFacts F E
  obtain ⟨iTG, iULC, iUSC, iUT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) G.V.J
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  have hσ : ∀ e, σ (σ e) = e := GlobalTheory.ThK.UnipDom.Inverse.sigma_sigma hB.cm
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hcc : ∀ z : AE F E, cA σ (cA σ z) = z := GlobalTheory.ThK.UnipDom.Inverse.cA_cA hσ

  have hLcl : IsClosed (GlobalTheory.UnipConj.imLine σ : Set (AE F E)) :=
    isClosed_eq (continuous_id.add hcA) continuous_const
  haveI : LocallyCompactSpace (GlobalTheory.UnipConj.imLine σ) := hLcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.UnipConj.imLine σ) := TopologicalSpace.Subtype.secondCountableTopology _
  letI mL : MeasurableSpace (GlobalTheory.UnipConj.imLine σ) := borel _
  haveI : BorelSpace (GlobalTheory.UnipConj.imLine σ) := ⟨rfl⟩
  letI mV : MeasurableSpace (Fin b → AE F E) := borel _
  haveI : BorelSpace (Fin b → AE F E) := ⟨rfl⟩

  obtain ⟨χ, hχ⟩ := GlobalTheory.T.unipotent_radical_coordinate_homeomorph F E σ B b a' G G₁ H H' hC hB hG hG₁
  haveI : LocallyCompactSpace (unip σ G.V H) := χ.isClosedEmbedding.locallyCompactSpace

  have hN := GlobalTheory.T.levi_normalizes_unipotent_radical F E σ B b a' G G₁ H H' hC hB hG hG₁ l g₀ h hL
  let φ : unip σ G.V H ≃ₜ* unip σ G.V H :=
    { toFun := fun n => ⟨h * n * h⁻¹, (hN n n.2).1⟩
      invFun := fun n => ⟨h⁻¹ * n * h, (hN n n.2).2⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun n m => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk (by fun_prop) _
      continuous_invFun := Continuous.subtype_mk (by fun_prop) _ }
  have hφ : ∀ n, (φ n : UA σ G.V.J) = h * n * h⁻¹ := fun n => rfl

  let wf : (Fin b → AE F E) → (Fin b → AE F E) → AE F E := fun a₁ a₂ => a₁ ⬝ᵥ GlobalTheory.UnipConj.betaOf σ G₁.V.J a₂
  have hwm : ∀ w : AE F E, w - cA σ w ∈ GlobalTheory.UnipConj.imLine σ := fun w => by
    rw [GlobalTheory.UnipConj.mem_imLine, map_sub, hcc]; abel
  let ω : (Fin b → AE F E) → (Fin b → AE F E) → GlobalTheory.UnipConj.imLine σ := fun a₁ a₂ => ⟨wf a₁ a₂ - cA σ (wf a₁ a₂), hwm _⟩
  have hbeta : Continuous (GlobalTheory.UnipConj.betaOf σ G₁.V.J) := by
    unfold GlobalTheory.UnipConj.betaOf
    exact continuous_pi fun i => (hcA.comp ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id))).neg
  have hwf : Continuous (fun p : (Fin b → AE F E) × (Fin b → AE F E) => wf p.1 p.2) :=
    continuous_fst.dotProduct (hbeta.comp continuous_snd)
  have hω : Continuous (fun p : (Fin b → AE F E) × (Fin b → AE F E) => ω p.1 p.2) :=
    Continuous.subtype_mk (hwf.sub (hcA.comp hwf)) _
  have hlaw : ∀ n₁ n₂ : unip σ G.V H, χ (n₁ * n₂) = ((χ n₁).1 + (χ n₂).1, (χ n₁).2 + (χ n₂).2 + ω (χ n₁).1 (χ n₂).1) := by
    intro n₁ n₂
    obtain ⟨e1, e2⟩ := GlobalTheory.T.unipotent_coordinate_additive_alt F E σ B b a' G G₁ H H' hC hB hG hG₁ n₁ n₁.2 n₂ n₂.2
    refine Prod.ext ?_ (Subtype.ext ?_)
    · rw [(hχ _).1, (hχ _).1, (hχ _).1]; exact e1
    · simp only [AddSubgroup.coe_add, (hχ _).2, (hχ _).1]
      show GlobalTheory.UnipConj.coT σ G.V.J H ((n₁ * n₂ : unip σ G.V H) : UA σ G.V.J) = _
      simp only [GlobalTheory.UnipConj.coT, Subgroup.coe_mul, e2, map_add]
      show _ = _ + _ + (wf _ _ - cA σ (wf _ _))
      abel

  have hg : ∀ a : Fin b → AE F E, (mat g₀)ᵀ *ᵥ ((mat g₀⁻¹)ᵀ *ᵥ a) = a := fun a => by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← GlobalTheory.ThK.UnipDom.Inverse.mat_mul, inv_mul_cancel,
      GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.transpose_one, Matrix.one_mulVec]
  have hg' : ∀ a : Fin b → AE F E, (mat g₀⁻¹)ᵀ *ᵥ ((mat g₀)ᵀ *ᵥ a) = a := fun a => by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← GlobalTheory.ThK.UnipDom.Inverse.mat_mul, mul_inv_cancel,
      GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.transpose_one, Matrix.one_mulVec]
  let A : (Fin b → AE F E) ≃ₜ+ (Fin b → AE F E) :=
    { toFun := fun a => l.1 • ((mat g₀⁻¹)ᵀ *ᵥ a)
      invFun := fun a => l⁻¹.1 • ((mat g₀)ᵀ *ᵥ a)
      left_inv := fun a => by
        simp only [Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul, hg]
      right_inv := fun a => by
        simp only [Matrix.mulVec_smul, smul_smul, Units.mul_inv, one_smul, hg']
      map_add' := fun a a' => by simp only [Matrix.mulVec_add, smul_add]
      continuous_toFun := (continuous_const_smul (l.1 : AE F E)).comp (continuous_const.matrix_mulVec continuous_id)
      continuous_invFun := by
        show Continuous fun a : Fin b → AE F E => (l⁻¹.1 : AE F E) • ((mat g₀)ᵀ *ᵥ a)
        exact (continuous_const_smul (l⁻¹.1 : AE F E)).comp (continuous_const.matrix_mulVec continuous_id) }
  have hmemB : ∀ (s : AE F E), s = cA σ s → ∀ t ∈ GlobalTheory.UnipConj.imLine σ, s * t ∈ GlobalTheory.UnipConj.imLine σ := by
    intro s hs t ht
    rw [GlobalTheory.UnipConj.mem_imLine] at ht ⊢
    rw [map_mul, ← hs, ← mul_add, ht, mul_zero]
  have hs1 : l.1 * cA σ l.1 = cA σ (l.1 * cA σ l.1) := by rw [map_mul, hcc, mul_comm]
  have hs2 : l⁻¹.1 * cA σ l⁻¹.1 = cA σ (l⁻¹.1 * cA σ l⁻¹.1) := by rw [map_mul, hcc, mul_comm]
  have hll : l⁻¹.1 * cA σ l⁻¹.1 * (l.1 * cA σ l.1) = 1 := by
    have : cA σ l⁻¹.1 * cA σ l.1 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    calc l⁻¹.1 * cA σ l⁻¹.1 * (l.1 * cA σ l.1) = (l⁻¹.1 * l.1) * (cA σ l⁻¹.1 * cA σ l.1) := by ring
      _ = 1 := by rw [this, Units.inv_mul, one_mul]
  have hll' : l.1 * cA σ l.1 * (l⁻¹.1 * cA σ l⁻¹.1) = 1 := by rw [mul_comm]; exact hll
  let Bl : GlobalTheory.UnipConj.imLine σ ≃ₜ+ GlobalTheory.UnipConj.imLine σ :=
    { toFun := fun t => ⟨l.1 * cA σ l.1 * t, hmemB _ hs1 t t.2⟩
      invFun := fun t => ⟨l⁻¹.1 * cA σ l⁻¹.1 * t, hmemB _ hs2 t t.2⟩
      left_inv := fun t => Subtype.ext (by simp only [← mul_assoc, hll, one_mul])
      right_inv := fun t => Subtype.ext (by simp only [← mul_assoc, hll', one_mul])
      map_add' := fun t t' => Subtype.ext (by simp only [AddSubgroup.coe_add, mul_add])
      continuous_toFun := Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _ }
  have hconj : ∀ n, χ (φ n) = (A (χ n).1, Bl (χ n).2) := by
    intro n
    obtain ⟨e1, e2⟩ := GlobalTheory.T.unipotent_coordinate_levi_conjugation F E σ B b a' G G₁ H H' hC hB hG hG₁ l g₀ h hL n
    refine Prod.ext ?_ (Subtype.ext ?_)
    · rw [(hχ _).1, (hχ _).1, hφ, e1]; rfl
    · rw [(hχ _).2]
      show GlobalTheory.UnipConj.coT σ G.V.J H (φ n : UA σ G.V.J) = l.1 * cA σ l.1 * ((χ n).2 : AE F E)
      rw [(hχ _).2, hφ]
      simp only [GlobalTheory.UnipConj.coT, e2, map_mul, hcc]
      ring
  have hdet : G₁.V.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have h1 := GlobalTheory.LeviElem.det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h1
    have e := (RingHom.map_det (B.emb w).1 G₁.V.J).symm
    rw [h0, map_zero] at e
    exact e
  have hchar : mulEquivHaarChar φ = absE F E l ^ (b + 1) := by
    rw [GlobalTheory.T.quotient_measure_fubini_locally_compact _ _ _ χ ω hω hlaw φ A Bl hconj, GlobalTheory.T.adelic_automorphism_measure_scaling F E σ hB.cm b G₁.V.J hdet l g₀ A (fun a => rfl),
      GlobalTheory.T.imaginary_line_measure_scaling F E σ hB.cm l Bl (fun t => rfl), pow_succ]

  have hne : absE F E l ≠ 0 := by
    intro h0
    have h1 := map_mul (absE F E) l l⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hc : mulEquivHaarChar φ ≠ 0 := by rw [hchar]; exact pow_ne_zero _ hne
  haveI : SecondCountableTopology (unip σ G.V H) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : T2Space (unip σ G.V H) := inferInstance
  haveI : μN.Regular := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  have hmap : μN.map φ = (mulEquivHaarChar φ)⁻¹ • μN := by
    conv_rhs => rw [← mulEquivHaarChar_smul_map μN φ]
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hfm : Measurable (f ∘ Subtype.val : unip σ G.V H → ℝ≥0∞) := hf.comp measurable_subtype_coe
  calc ∫⁻ n, f (h * n.1 * h⁻¹) ∂μN = ∫⁻ n, (f ∘ Subtype.val) (φ n) ∂μN := rfl
    _ = ∫⁻ m, (f ∘ Subtype.val) m ∂(μN.map φ) := (lintegral_map hfm φ.continuous.measurable).symm
    _ = ((absE F E l : ℝ≥0∞) ^ (b + 1))⁻¹ * ∫⁻ n, f n.1 ∂μN := by
      rw [hmap, lintegral_smul_measure, hchar]
      simp only [ENNReal.smul_def, smul_eq_mul, Function.comp_apply]
      congr 1
      rw [ENNReal.coe_inv (pow_ne_zero _ hne), ENNReal.coe_pow]
