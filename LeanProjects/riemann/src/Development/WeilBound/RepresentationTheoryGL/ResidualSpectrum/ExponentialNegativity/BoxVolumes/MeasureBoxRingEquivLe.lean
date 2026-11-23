import Mathlib
import GroundTheory.AutomorphicForms.ReductionLocalVolume
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.MeasureBoxGLLe

open MeasureTheory Measure Set Matrix NumberField
open scoped NNReal ENNReal
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace PositivityTheory.Rg.Rs.boxvol

section Transport

variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {m : ℕ}
  [MeasurableSpace (GL (Fin (m + 1)) E)] [BorelSpace (GL (Fin (m + 1)) E)]
  [MeasurableSpace (GL (Fin (m + 1)) 𝕜)] [BorelSpace (GL (Fin (m + 1)) 𝕜)]

theorem measure_box_ringEquiv_le (φ : E ≃+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
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
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) E).IsUpperTriangular) (B : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x : Fin (m + 1) → ℝ,
      μ {g | ∃ b ∈ ω, ∃ y : Fin (m + 1) → ℝ, (∀ i, |y i| ≤ B) ∧ ∃ k : GL (Fin (m + 1)) E,
        (∀ z : Fin (m + 1) → E, euclidNorm (z ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) = euclidNorm z) ∧
        g = b * D ⟨fun i => Real.exp (x i + y i), fun _ => Real.exp_pos _⟩ * k} ≤
        C * ENNReal.ofReal (Real.exp (-((Module.finrank ℝ 𝕜 : ℝ) * pairSum m x))) := by
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
  obtain ⟨C, hC, hCb⟩ := measure_boxGL_le ν (fun μK _ μA _ μN _ => hANK ν μK μA μN) hω' hωB' B
  refine ⟨C, hC, fun x => le_trans ?_ (hCb x)⟩
  refine (measure_mono ?_).trans (Measure.le_map_apply Φ.continuous.measurable.aemeasurable _)
  rintro g ⟨b, hbω, y, hy, k, hk, rfl⟩
  change Φ (b * D _ * k) ∈ boxGL (Φ '' ω) B x
  have hkU : ((Φ k : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) ∈
      unitaryGroup (Fin (m + 1)) 𝕜 := by
    refine mem_unitaryGroup_of_euclidNorm fun z => ?_
    have hz : z = fun i => φ (φ.symm (z i)) := by funext i; simp
    rw [hz, hΦv]
    have : (fun i => φ (φ.symm (z i))) ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ =
        fun j => φ.toRingHom (((fun i => φ.symm (z i)) ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) j) := by
      ext j
      simp [vecMul, dotProduct, _root_.map_sum, map_mul]
    rw [this, euclidNorm_map φ.toRingHom hφ, hk, ← euclidNorm_map φ.toRingHom hφ]
    rfl
  refine ⟨Φ b, ⟨b, hbω, rfl⟩, y, hy, ⟨_, hkU⟩, ?_⟩
  rw [map_mul, map_mul]
  congr 1
  · congr 1
    apply Units.ext
    rw [hΦv, hD, coe_diagPosOf]
  · apply Units.ext
    rfl

end Transport

variable {K : Type*} [Field K] {m : ℕ}

def boxPlace (w : InfinitePlace K) (ω : Set (GL (Fin (m + 1)) w.Completion)) (B : ℝ) (x : Fin (m + 1) → ℝ) :
    Set (GL (Fin (m + 1)) w.Completion) :=
  {g | ∃ b ∈ ω, ∃ y : Fin (m + 1) → ℝ, (∀ i, |y i| ≤ B) ∧ ∃ k ∈ archCompact w,
    g = b * diagUnits (m + 1) (fun i => posRealToUnits w
      ⟨Real.exp (x i + y i) ^ w.mult, pow_pos (Real.exp_pos _) _⟩) * k}

theorem measure_boxPlace_le (w : InfinitePlace K)
    [MeasurableSpace (GL (Fin (m + 1)) w.Completion)] [BorelSpace (GL (Fin (m + 1)) w.Completion)]
    (μ : Measure (GL (Fin (m + 1)) w.Completion)) [μ.IsHaarMeasure]
    {ω : Set (GL (Fin (m + 1)) w.Completion)} (hω : IsCompact ω)
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).IsUpperTriangular) (B : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x : Fin (m + 1) → ℝ,
      μ (boxPlace w ω B x) ≤ C * ENNReal.ofReal (Real.exp (-((w.mult : ℝ) * pairSum m x))) := by
  classical
  set D : PosDiag (Fin (m + 1)) → GL (Fin (m + 1)) w.Completion := fun r =>
    diagUnits (m + 1) (fun i => posRealToUnits w ⟨r.1 i ^ w.mult, pow_pos (r.2 i) _⟩) with hDdef
  have hsub : ∀ x, boxPlace w ω B x ⊆
      {g | ∃ b ∈ ω, ∃ y : Fin (m + 1) → ℝ, (∀ i, |y i| ≤ B) ∧ ∃ k : GL (Fin (m + 1)) w.Completion,
        (∀ z : Fin (m + 1) → w.Completion,
          euclidNorm (z ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion)) = euclidNorm z) ∧
        g = b * D ⟨fun i => Real.exp (x i + y i), fun i => Real.exp_pos _⟩ * k} := by
    rintro x g ⟨b, hb, y, hy, k, hk, rfl⟩
    exact ⟨b, hb, y, hy, k, hk, rfl⟩
  by_cases hw : w.IsReal
  · have hφ : ∀ x, ‖InfinitePlace.Completion.ringEquivRealOfIsReal hw x‖ = ‖x‖ := fun x =>
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) x
    have hm : w.mult = 1 := by simp [InfinitePlace.mult, hw]
    have hD : ∀ r : PosDiag (Fin (m + 1)), ((D r : GL (Fin (m + 1)) w.Completion) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).map (InfinitePlace.Completion.ringEquivRealOfIsReal hw) =
        diagonal fun i => ((r.1 i : ℝ) : ℝ) := fun r => by
      rw [hDdef]
      dsimp only
      rw [coe_diagUnits, diagonal_map (map_zero _)]
      congr 1
      funext i
      simp only [posRealToUnits, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, posRealElem,
        dif_pos hw, RingEquiv.apply_symm_apply, hm, pow_one]
    obtain ⟨C, hC, hCb⟩ := measure_box_ringEquiv_le (𝕜 := ℝ)
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw) hφ
      (fun ν _ μK _ μA _ μN _ => lintegral_GLReal_ANK ν μK μA μN) μ D hD hω hωB B
    refine ⟨C, hC, fun x => (measure_mono (hsub x)).trans ?_⟩
    have h := hCb x
    rw [Module.finrank_self] at h
    rwa [hm]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have hφ : ∀ x, ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex hc x‖ = ‖x‖ := fun x =>
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
    have hm : w.mult = 2 := by simp [InfinitePlace.mult, hw]
    have hD : ∀ r : PosDiag (Fin (m + 1)), ((D r : GL (Fin (m + 1)) w.Completion) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) =
        diagonal fun i => ((r.1 i : ℝ) : ℂ) := fun r => by
      rw [hDdef]
      dsimp only
      rw [coe_diagUnits, diagonal_map (map_zero _)]
      congr 1
      funext i
      simp only [posRealToUnits, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, posRealElem,
        dif_neg hw, RingEquiv.apply_symm_apply, hm]
      rw [Real.sqrt_sq (r.2 i).le]
    obtain ⟨C, hC, hCb⟩ := measure_box_ringEquiv_le (𝕜 := ℂ)
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) hφ
      (fun ν _ μK _ μA _ μN _ => lintegral_GLComplex_ANK ν μK μA μN) μ D hD hω hωB B
    refine ⟨C, hC, fun x => (measure_mono (hsub x)).trans ?_⟩
    have h := hCb x
    rw [Complex.finrank_real_complex] at h
    rwa [hm]

end PositivityTheory.Rg.Rs.boxvol

end
