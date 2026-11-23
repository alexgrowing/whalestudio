import Mathlib
import GroundTheory.AutomorphicForms.ReductionLocalVolumeGL
import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.RestrictedProductMatrix
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne

open MeasureTheory Measure Set Matrix NumberField
open scoped NNReal ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem mem_unitaryGroup_of_euclidNorm {M : Matrix (Fin n) (Fin n) 𝕜}
    (hM : ∀ y : Fin n → 𝕜, euclidNorm (y ᵥ* M) = euclidNorm y) : M ∈ unitaryGroup (Fin n) 𝕜 := by
  classical
  let L : EuclideanSpace 𝕜 (Fin n) →ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    { toFun := fun x => WithLp.toLp 2 (WithLp.ofLp x ᵥ* M)
      map_add' := fun x y => by simp [add_vecMul]
      map_smul' := fun c x => by simp [smul_vecMul]
      norm_map' := fun x => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        exact hM (WithLp.ofLp x) }
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have h := L.inner_map_map (WithLp.toLp 2 (Pi.single j (1 : 𝕜))) (WithLp.toLp 2 (Pi.single i (1 : 𝕜)))
  simp only [L, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    EuclideanSpace.inner_toLp_toLp, single_one_vecMul] at h
  rw [Matrix.mul_apply, one_apply]
  have h2 : ∑ k, M i k * star M k j = M.row i ⬝ᵥ star (M.row j) := by
    simp [dotProduct, Matrix.row, Matrix.star_apply]
  rw [h2, h, single_one_dotProduct, Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

end Unitary

section Transport

variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {m : ℕ}
  [MeasurableSpace (GL (Fin (m + 1)) E)] [BorelSpace (GL (Fin (m + 1)) E)]
  [MeasurableSpace (GL (Fin (m + 1)) 𝕜)] [BorelSpace (GL (Fin (m + 1)) 𝕜)]

theorem measure_lt_top_of_ringEquiv (φ : E ≃+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
    [MeasurableSpace (unitaryGroup (Fin (m + 1)) 𝕜)] [BorelSpace (unitaryGroup (Fin (m + 1)) 𝕜)]
    (hANK : ∀ (ν : Measure (GL (Fin (m + 1)) 𝕜)) [ν.IsHaarMeasure]
      (μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜)) [μK.IsHaarMeasure]
      (μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜)) [μA.IsHaarMeasure]
      (μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜)) [μN.IsHaarMeasure],
      ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂ν = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA)
    (μ : Measure (GL (Fin (m + 1)) E)) [μ.IsHaarMeasure]
    (D : PosDiag (Fin (m + 1)) → GL (Fin (m + 1)) E)
    (hD : ∀ r, ((D r : GL (Fin (m + 1)) E) : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ =
      diagonal fun i => ((r.1 i : ℝ) : 𝕜))
    {ω : Set (GL (Fin (m + 1)) E)} (hω : IsCompact ω)
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) E).IsUpperTriangular)
    {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁) :
    μ {g | c₁ ≤ ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) E).det‖ ∧
      ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) E).det‖ ≤ c₂ ∧
      ∃ b ∈ ω, ∃ r : PosDiag (Fin (m + 1)), (∀ l : Fin m, t * r.1 l.succ ≤ r.1 l.castSucc) ∧
        ∃ k : GL (Fin (m + 1)) E, (∀ y : Fin (m + 1) → E,
          euclidNorm (y ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) = euclidNorm y) ∧
          g = b * D r * k} < ⊤ := by
  classical
  have hφc : Continuous φ := (AddMonoidHomClass.isometry_of_norm φ hφ).continuous
  have hφ' : ∀ x, ‖φ.symm x‖ = ‖x‖ := fun x => by rw [← hφ, RingEquiv.apply_symm_apply]
  have hφc' : Continuous φ.symm := (AddMonoidHomClass.isometry_of_norm φ.symm hφ').continuous
  set e : Matrix (Fin (m + 1)) (Fin (m + 1)) E ≃* Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
    φ.mapMatrix.toMulEquiv with he
  set Φ : GL (Fin (m + 1)) E ≃ₜ* GL (Fin (m + 1)) 𝕜 :=
    unitsCongr e (continuous_id.matrix_map hφc) (continuous_id.matrix_map hφc') with hΦ
  have hΦv : ∀ g : GL (Fin (m + 1)) E,
      ((Φ g : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ := fun g => rfl
  set ν : Measure (GL (Fin (m + 1)) 𝕜) := Measure.map Φ μ with hν
  have hνH : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ Φ
  have hω' : IsCompact (Φ '' ω) := hω.image Φ.continuous
  have hωB' : ∀ b ∈ Φ '' ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).IsUpperTriangular := by
    rintro _ ⟨b, hb, rfl⟩ i j hij
    rw [hΦv, Matrix.map_apply, hωB b hb hij, map_zero]
  have hfin := measure_siegelGL_lt_top (c₂ := c₂) ν (fun μK _ μA _ μN _ => hANK ν μK μA μN) hω' hωB'
    ht hc₁
  have hmeas : MeasurableSet (siegelGL (Φ '' ω) t c₁ c₂) := (isClosed_siegelGL hω' t c₁ c₂).measurableSet
  refine lt_of_le_of_lt (measure_mono ?_) ((Measure.map_apply Φ.continuous.measurable hmeas).symm ▸
    hfin)
  rintro g ⟨hd1, hd2, b, hbω, r, hr, k, hk, rfl⟩
  change Φ (b * D r * k) ∈ siegelGL (Φ '' ω) t c₁ c₂
  have hdet : ‖((Φ (b * D r * k) : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).det‖ =
      ‖((b * D r * k : GL (Fin (m + 1)) E) : Matrix (Fin (m + 1)) (Fin (m + 1)) E).det‖ := by
    rw [hΦv]
    have h1 := RingHom.map_det (φ : E →+* 𝕜) ((b * D r * k : GL (Fin (m + 1)) E) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) E)
    rw [RingHom.mapMatrix_apply] at h1
    change ‖(((b * D r * k : GL (Fin (m + 1)) E) : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map
      (φ : E →+* 𝕜)).det‖ = _
    rw [← h1]
    exact hφ _
  have hkU : ((Φ k : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) ∈
      unitaryGroup (Fin (m + 1)) 𝕜 := by
    refine mem_unitaryGroup_of_euclidNorm fun y => ?_
    have hy : y = fun i => φ (φ.symm (y i)) := by funext i; simp
    rw [hy, hΦv]
    have : (fun i => φ (φ.symm (y i))) ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ =
        fun j => φ.toRingHom (((fun i => φ.symm (y i)) ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) j) := by
      ext j
      simp [vecMul, dotProduct, _root_.map_sum, map_mul]
    rw [this, euclidNorm_map φ.toRingHom hφ, hk, ← euclidNorm_map φ.toRingHom hφ]
    rfl
  refine ⟨hd1.trans_eq hdet.symm, hdet.trans_le hd2, Φ b, ⟨b, hbω, rfl⟩, r, hr,
    ⟨_, hkU⟩, ?_⟩
  rw [map_mul, map_mul]
  congr 1
  · congr 1
    apply Units.ext
    rw [hΦv, hD, coe_diagPosOf]
  · apply Units.ext
    rfl

end Transport

section Place

open GroundTheory.Global

variable {K : Type*} [Field K]

def localSiegel (w : InfinitePlace K) {n : ℕ} (ω : Set (GL (Fin n) w.Completion)) (t c₁ c₂ : ℝ) :
    Set (GL (Fin n) w.Completion) :=
  {g | c₁ ≤ ‖(g : Matrix (Fin n) (Fin n) w.Completion).det‖ ∧
    ‖(g : Matrix (Fin n) (Fin n) w.Completion).det‖ ≤ c₂ ∧
    ∃ b ∈ ω, ∃ (r : Fin n → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧
      ∃ k ∈ archCompact w,
        g = b * diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) * k}

theorem measure_localSiegel_lt_top (w : InfinitePlace K) {n : ℕ}
    [MeasurableSpace (GL (Fin n) w.Completion)] [BorelSpace (GL (Fin n) w.Completion)]
    (μ : Measure (GL (Fin n) w.Completion)) [μ.IsHaarMeasure] {ω : Set (GL (Fin n) w.Completion)}
    (hω : IsCompact ω) (hωB : ∀ b ∈ ω, (b : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular)
    {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁) : μ (localSiegel w ω t c₁ c₂) < ⊤ := by
  classical
  cases n with
  | zero =>
    have hs : (Set.univ : Set (GL (Fin 0) w.Completion)).Subsingleton := fun x _ y _ =>
      Units.ext (Subsingleton.elim _ _)
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) hs.isCompact.measure_lt_top
  | succ m =>
    set D : PosDiag (Fin (m + 1)) → GL (Fin (m + 1)) w.Completion := fun r =>
      diagUnits (m + 1) (fun i => posRealToUnits w ⟨r.1 i ^ w.mult, pow_pos (r.2 i) _⟩) with hDdef
    have hsub : localSiegel w ω t c₁ c₂ ⊆
        {g | c₁ ≤ ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).det‖ ∧
          ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).det‖ ≤ c₂ ∧
          ∃ b ∈ ω, ∃ r : PosDiag (Fin (m + 1)), (∀ l : Fin m, t * r.1 l.succ ≤ r.1 l.castSucc) ∧
            ∃ k : GL (Fin (m + 1)) w.Completion, (∀ y : Fin (m + 1) → w.Completion,
              euclidNorm (y ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion)) = euclidNorm y) ∧
              g = b * D r * k} := by
      rintro g ⟨h1, h2, b, hb, r, hr, hrat, k, hk, rfl⟩
      exact ⟨h1, h2, b, hb, ⟨r, hr⟩, fun l => hrat l.castSucc l.succ (by simp), k, hk, rfl⟩
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    by_cases hw : w.IsReal
    · have hφ : ∀ x, ‖InfinitePlace.Completion.ringEquivRealOfIsReal hw x‖ = ‖x‖ := fun x =>
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) x
      refine measure_lt_top_of_ringEquiv (𝕜 := ℝ)
        (InfinitePlace.Completion.ringEquivRealOfIsReal hw) hφ
        (fun ν _ μK _ μA _ μN _ => lintegral_GLReal_ANK ν μK μA μN) μ D (fun r => ?_) hω hωB ht hc₁
      rw [hDdef]
      dsimp only
      rw [coe_diagUnits, diagonal_map (map_zero _)]
      congr 1
      funext i
      have hm : w.mult = 1 := by simp [InfinitePlace.mult, hw]
      simp only [posRealToUnits, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, posRealElem,
        dif_pos hw, RingEquiv.apply_symm_apply, hm, pow_one]
      rfl
    · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
      have hφ : ∀ x, ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex hc x‖ = ‖x‖ := fun x =>
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
      refine measure_lt_top_of_ringEquiv (𝕜 := ℂ)
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) hφ
        (fun ν _ μK _ μA _ μN _ => lintegral_GLComplex_ANK ν μK μA μN) μ D (fun r => ?_) hω hωB ht hc₁
      rw [hDdef]
      dsimp only
      rw [coe_diagUnits, diagonal_map (map_zero _)]
      congr 1
      funext i
      have hm : w.mult = 2 := by simp [InfinitePlace.mult, hw]
      simp only [posRealToUnits, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, posRealElem,
        dif_neg hw, RingEquiv.apply_symm_apply, hm]
      rw [Real.sqrt_sq (r.2 i).le]
      rfl

end Place

end Reduction

end

end GroundTheory.Automorphic
