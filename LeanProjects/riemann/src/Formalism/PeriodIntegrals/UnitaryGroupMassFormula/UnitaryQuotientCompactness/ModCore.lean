import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModBase

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW

open PI MG

variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}

theorem map_mul_right_haar (g : MG G hG) :
    (Measure.haar : Measure (MG G hG)).map (· * g) =
      Measure.modularCharacterFun g • (Measure.haar : Measure (MG G hG)) := by
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure (MG G hG)) g]
  exact Measure.isMulLeftInvariant_eq_smul_of_regular _ _

private theorem isEmbedding_MG_val : Topology.IsEmbedding (MG.val : MG G hG → MtM m) :=
  ⟨⟨rfl⟩, fun _ _ hxy => Subtype.ext hxy⟩

private theorem measurableEmbedding_MG_val :
    MeasurableEmbedding (MG.val : MG G hG → MtM m) := by
  have hr : Set.range (MG.val : MG G hG → MtM m) = {x | Matrix.of x ∈ G} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hc : IsClosed (Set.range (MG.val : MG G hG → MtM m)) := by
    rw [hr]
    exact hG.1.preimage (f := fun x : MtM m => Matrix.of x) continuous_id
  exact (Topology.IsClosedEmbedding.mk isEmbedding_MG_val hc).measurableEmbedding

theorem onG_eq (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) :
    ∃ c : ℝ≥0∞, onG hG μ = c • (Measure.haar : Measure (MG G hG)) := by
  haveI := hμ.1
  have hMe : MeasurableEmbedding (MG.val : MG G hG → MtM m) := measurableEmbedding_MG_val
  haveI : SigmaFinite (onG hG μ) := by
    refine ⟨⟨⟨fun n => MG.val ⁻¹' spanningSets μ n, fun _ => Set.mem_univ _, fun n => ?_, ?_⟩⟩⟩
    · show μ.comap MG.val _ < ⊤
      rw [hMe.comap_apply]
      exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)
    · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  have hkey : ∀ h z : MG G hG, MG.val (h * z) = lmulQ (MG.toM h) (MG.val z) := by
    intro h z
    show MG.toM (h * z) = _
    rw [toM_mul']
    rfl
  haveI : Measure.IsMulLeftInvariant (onG hG μ) := by
    refine ⟨fun h => Measure.ext fun s hs => ?_⟩
    have hA : Measurable (lmulQ (MG.toM h) : MtM m → MtM m) := by
      refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
      have hf : (fun x : MtM m => lmulQ (MG.toM h) x i j) = fun x => ∑ k, MG.toM h i k * x k j := by
        funext x
        simp only [lmulQ, Matrix.mul_apply, Matrix.of_apply]
      rw [hf]
      exact continuous_finset_sum _ fun k _ => by fun_prop
    have hvs : MeasurableSet (MG.val '' s) := hMe.measurableSet_image.2 hs
    have hinvA : Measure.map (lmulQ (MG.toM h)) μ = μ := hμ.2.2.2 _ h.2
    rw [Measure.map_apply (measurable_const_mul h) hs]
    show μ.comap MG.val _ = μ.comap MG.val _
    rw [hMe.comap_apply, hMe.comap_apply]
    apply le_antisymm
    · calc μ (MG.val '' ((h * ·) ⁻¹' s)) ≤ μ (lmulQ (MG.toM h) ⁻¹' (MG.val '' s)) := by
            apply measure_mono
            rintro _ ⟨z, hz, rfl⟩
            exact ⟨h * z, hz, hkey h z⟩
        _ = μ (MG.val '' s) := by
            rw [← Measure.map_apply hA hvs, hinvA]
    · calc μ (MG.val '' s) = μ (lmulQ (MG.toM h) ⁻¹' (MG.val '' s)) := by
            rw [← Measure.map_apply hA hvs, hinvA]
        _ ≤ μ (MG.val '' ((h * ·) ⁻¹' s) ∪ {x | Matrix.of x ∉ G}) := by
            apply measure_mono
            intro y hy
            by_cases hyG : Matrix.of y ∈ G
            · left
              obtain ⟨w, hw, hwy⟩ := hy
              obtain ⟨z, hz⟩ : ∃ z : MG G hG, MG.val z = y := ⟨⟨y, hyG⟩, rfl⟩
              refine ⟨z, ?_, hz⟩
              have hEq : h * z = w := by
                apply hMe.injective
                rw [hkey, hz, hwy]
              show h * z ∈ s
              rw [hEq]
              exact hw
            · right
              exact hyG
        _ ≤ μ (MG.val '' ((h * ·) ⁻¹' s)) + μ {x | Matrix.of x ∉ G} := measure_union_le _ _
        _ = μ (MG.val '' ((h * ·) ⁻¹' s)) := by rw [hμ.2.2.1, add_zero]
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (MG G hG)) := inferInstance
  have hK0 : (Measure.haar : Measure (MG G hG)) K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hKt : (Measure.haar : Measure (MG G hG)) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  exact ⟨_, measure_eq_div_smul (onG hG μ) Measure.haar hK0 hKt⟩

theorem rightInv_of (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ)
    (h1 : ∀ g : MG G hG, Measure.modularCharacterFun g = 1) : IsRightInvM G μ := by
  obtain ⟨c, hc⟩ := onG_eq μ hμ
  have hMe : MeasurableEmbedding (MG.val : MG G hG → MtM m) := measurableEmbedding_MG_val
  have hback : Measure.map MG.val (onG hG μ) = μ := by
    show Measure.map MG.val (μ.comap MG.val) = μ
    rw [hMe.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have hset : {x | ¬ x ∈ Set.range (MG.val : MG G hG → MtM m)} = {x | Matrix.of x ∉ G} := by
      ext x
      constructor
      · intro hx hxG
        exact hx ⟨⟨x, hxG⟩, rfl⟩
      · rintro hx ⟨z, rfl⟩
        exact hx z.2
    rw [hset]
    exact hμ.2.2.1
  intro s hs
  have hR : Measurable (rmulQ s : MtM m → MtM m) := by
    refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
    have hf : (fun x : MtM m => rmulQ s x i j) = fun x => ∑ k, x i k * s k j := by
      funext x
      simp only [rmulQ, Matrix.mul_apply, Matrix.of_apply]
    rw [hf]
    exact continuous_finset_sum _ fun k _ => by fun_prop
  have hgkey : (rmulQ s) ∘ MG.val = MG.val ∘ (· * mk hG s hs) := by
    funext z
    show _ = MG.toM (z * mk hG s hs)
    rw [toM_mul', toM_mk]
    rfl
  have hinv : Measure.map (· * mk hG s hs) (onG hG μ) = onG hG μ := by
    rw [hc, Measure.map_smul, map_mul_right_haar, h1, one_smul]
  rw [← hback, Measure.map_map hR hMe.measurable, hgkey,
    ← Measure.map_map hMe.measurable (measurable_mul_const _), hinv]

def conjE (c : Matrix (Fin m) (Fin m) ℂ) (hc : IsUnit c) (hcG : ∀ g, c * g * c⁻¹ ∈ G ↔ g ∈ G) :
    MG G hG ≃ₜ* MG G hG where
  toFun x := mk hG (c * x.toM * c⁻¹) ((hcG _).2 x.2)
  invFun x := mk hG (c⁻¹ * x.toM * c) (by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    apply (hcG _).1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    exact x.2)
  left_inv x := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    ext1
    simp only [toM_mk]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  right_inv x := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    ext1
    simp only [toM_mk]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  map_mul' x y := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    ext1
    simp only [toM_mk, toM_mul']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc c⁻¹ c, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  continuous_toFun := by
    rw [continuous_iff_toM]
    simp only [toM_mk]
    exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const
  continuous_invFun := by
    rw [continuous_iff_toM]
    simp only [toM_mk]
    exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const

theorem modF_conj (φ : MG G hG ≃ₜ* MG G hG) (g : MG G hG) :
    Measure.modularCharacterFun (φ g) = Measure.modularCharacterFun g := by
  rw [Measure.modularCharacterFun_eq_haarScalarFactor
    (Measure.map φ (Measure.haar : Measure (MG G hG))) (φ g)]
  have hφ : Measurable φ := φ.continuous.measurable
  have e1 : Measure.map (· * φ g) (Measure.map φ (Measure.haar : Measure (MG G hG)))
      = Measure.modularCharacterFun g • Measure.map φ (Measure.haar : Measure (MG G hG)) := by
    rw [Measure.map_map (measurable_mul_const (φ g)) hφ]
    have e : ((· * φ g) ∘ ⇑φ) = (⇑φ ∘ (· * g)) := by
      funext x
      simp [map_mul]
    rw [e, ← Measure.map_map hφ (measurable_mul_const g), map_mul_right_haar g, Measure.map_smul]
  simp only [e1, Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul, mul_one]

theorem modF_bdd (V : Set (MG G hG)) (hV : IsCompact V) :
    ∃ M : ℝ, ∀ v ∈ V, (Measure.modularCharacterFun v : ℝ) ≤ M := by
  have K : TopologicalSpace.PositiveCompacts (MG G hG) := Classical.arbitrary _
  set C : Set (MG G hG) :=
    (fun p : MG G hG × MG G hG => p.1 * p.2⁻¹) '' ((K : Set (MG G hG)) ×ˢ V) with hCdef
  have hC : IsCompact C := (K.isCompact.prod hV).image (continuous_fst.mul continuous_snd.inv)
  have hK0 : 0 < (Measure.haar : Measure (MG G hG)) K :=
    Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty
  have hKt : (Measure.haar : Measure (MG G hG)) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hCt : (Measure.haar : Measure (MG G hG)) C ≠ ⊤ := hC.measure_lt_top.ne
  refine ⟨((Measure.haar : Measure (MG G hG)) C / (Measure.haar : Measure (MG G hG)) K).toReal,
    fun v hv => ?_⟩
  have h := (MeasurableEquiv.mulRight v).map_apply (μ := (Measure.haar : Measure (MG G hG)))
    (K : Set (MG G hG))
  rw [MeasurableEquiv.coe_mulRight, map_mul_right_haar v, Measure.smul_apply, ENNReal.smul_def] at h
  have hsub : (fun x => x * v) ⁻¹' (K : Set (MG G hG)) ⊆ C := by
    intro x hx
    exact ⟨(x * v, v), ⟨hx, hv⟩, by simp⟩
  have hle : (Measure.modularCharacterFun v : ℝ≥0∞) * (Measure.haar : Measure (MG G hG)) K
      ≤ (Measure.haar : Measure (MG G hG)) C := by
    rw [← smul_eq_mul, h]
    exact measure_mono hsub
  have hle' : (Measure.modularCharacterFun v : ℝ≥0∞)
      ≤ (Measure.haar : Measure (MG G hG)) C / (Measure.haar : Measure (MG G hG)) K :=
    (ENNReal.le_div_iff_mul_le (Or.inl hK0.ne') (Or.inl hKt)).2 hle
  rw [← ENNReal.coe_toReal]
  exact ENNReal.toReal_mono (ENNReal.div_ne_top hCt hK0.ne') hle'

end PI.QuotSetU.UnitaryGroupMassFormula.ModW
