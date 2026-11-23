import Mathlib
import GroundTheory.AutomorphicForms.GL2.GodementSection
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology NumberField.mixedEmbedding
open scoped NumberField.AdeleRing SchwartzMap Classical

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def infChar (χ : HeckeCharacter K) : (InfiniteAdeleRing K)ˣ →* Circle :=
  χ.toIdele.comp ofInfinite

def finChar (χ : HeckeCharacter K) : (FiniteAdeleRing (𝓞 K) K)ˣ →* Circle :=
  χ.toIdele.comp ofFinite

def infMod (a : (InfiniteAdeleRing K)ˣ) : ℝ :=
  ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult

def finMod (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(b : FiniteAdeleRing (𝓞 K) K) v‖

theorem infMod_pos (a : (InfiniteAdeleRing K)ˣ) : 0 < infMod a :=
  infiniteModule_pos (ofInfinite a)

theorem finMod_pos (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : 0 < finMod b :=
  finiteModule_pos (ofFinite b)

theorem toIdele_eq_finChar_mul_infChar (χ : HeckeCharacter K) (x : IdeleGroup K) :
    χ.toIdele x = finChar χ (toFinite K x) * infChar χ (toInfinite K x) := by
  rw [finChar, infChar, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul,
    ofFinite_mul_ofInfinite]

theorem ideleModule_eq_infMod_mul_finMod (x : IdeleGroup K) :
    (ideleModule K x : ℝ) = infMod (toInfinite K x) * finMod (toFinite K x) := rfl

theorem modPow_eq (x : IdeleGroup K) (s : ℂ) :
    modPow x s = ((infMod (toInfinite K x) : ℝ) : ℂ) ^ s * ((finMod (toFinite K x) : ℝ) : ℂ) ^ s := by
  rw [modPow, ideleModule_eq_infMod_mul_finMod, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (infMod_pos _).le (finMod_pos _).le s

def infVec (y : Fin 2 → InfiniteAdeleRing K) : Fin 2 → mixedSpace K :=
  fun i ↦ homeomorphMixedSpace K (y i)

def archSection (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (φ : (Fin 2 → mixedSpace K) → ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) : ℂ :=
  (infChar χ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
    ((infMod (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s *
      ∫ a, φ (infVec (![0, (a : InfiniteAdeleRing K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)))) *
        (infChar (χ₁ * χ₂⁻¹) a : ℂ) * ((infMod a : ℝ) : ℂ) ^ (2 * s) ∂infiniteIdeleMeasure K

def finSection (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (Φ : (Fin 2 → FiniteAdeleRing (𝓞 K) K) → ℂ)
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : ℂ :=
  (finChar χ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
    ((finMod (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s *
      ∫ b, Φ (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) *
        (finChar (χ₁ * χ₂⁻¹) b : ℂ) * ((finMod b : ℝ) : ℂ) ^ (2 * s) ∂finiteIdeleMeasure K

theorem val_symm_fst (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (((IdeleGroup.prodEquiv K).symm p : IdeleGroup K) : 𝔸[K]).1 = (p.1 : InfiniteAdeleRing K) := by
  rw [← IdeleGroup.prodEquiv_apply_fst, ContinuousMulEquiv.apply_symm_apply]

theorem val_symm_snd (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (((IdeleGroup.prodEquiv K).symm p : IdeleGroup K) : 𝔸[K]).2 =
      (p.2 : FiniteAdeleRing (𝓞 K) K) := by
  rw [← IdeleGroup.prodEquiv_apply_snd, ContinuousMulEquiv.apply_symm_apply]

theorem toInfinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toInfinite K ((IdeleGroup.prodEquiv K).symm p) = p.1 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).1 = p.1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem toFinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toFinite K ((IdeleGroup.prodEquiv K).symm p) = p.2 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).2 = p.2
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem toInfinite_detI (g : GL (Fin 2) 𝔸[K]) :
    toInfinite K (detI g) = Matrix.GeneralLinearGroup.det (AdelicGLn.prodEquiv K 2 g).1 := by
  apply Units.ext
  change ((detI g : IdeleGroup K) : 𝔸[K]).1 = _
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, Matrix.det_fin_two]
  simp [AdelicGLn.prodEquiv_apply_fst]

theorem toFinite_detI (g : GL (Fin 2) 𝔸[K]) :
    toFinite K (detI g) = Matrix.GeneralLinearGroup.det (AdelicGLn.prodEquiv K 2 g).2 := by
  apply Units.ext
  change ((detI g : IdeleGroup K) : 𝔸[K]).2 = _
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, Matrix.det_fin_two]
  simp [AdelicGLn.prodEquiv_apply_snd]

theorem infPart_slice (g : GL (Fin 2) 𝔸[K]) (t : 𝔸[K]) :
    infPart (![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])) =
      infVec (![0, t.1] ᵥ* ((AdelicGLn.prodEquiv K 2 g).1 :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) := by
  funext i
  simp only [infPart, infVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  congr 1

theorem finPart_slice (g : GL (Fin 2) 𝔸[K]) (t : 𝔸[K]) :
    finPart (![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])) =
      ![0, t.2] ᵥ* ((AdelicGLn.prodEquiv K 2 g).2 :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  funext i
  simp [finPart, Matrix.vecMul, dotProduct, Fin.sum_univ_two, AdelicGLn.prodEquiv_apply_snd]

theorem godementSection_tensor (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (φ : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (Φ : (Fin 2 → FiniteAdeleRing (𝓞 K) K) → ℂ) (g : GL (Fin 2) 𝔸[K]) :
    godementSection χ₁ χ₂ s (schwartzBruhatTensor2 φ Φ) g =
      archSection χ₁ χ₂ s φ (AdelicGLn.prodEquiv K 2 g).1 *
        finSection χ₁ χ₂ s Φ (AdelicGLn.prodEquiv K 2 g).2 := by
  have hZ : globalZeta (slice (schwartzBruhatTensor2 φ Φ) g) (χ₁ * χ₂⁻¹) (2 * s) =
      (∫ a, φ (infVec (![0, (a : InfiniteAdeleRing K)] ᵥ*
          ((AdelicGLn.prodEquiv K 2 g).1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)))) *
        (infChar (χ₁ * χ₂⁻¹) a : ℂ) * ((infMod a : ℝ) : ℂ) ^ (2 * s) ∂infiniteIdeleMeasure K) *
      ∫ b, Φ (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ*
          ((AdelicGLn.prodEquiv K 2 g).2 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) *
        (finChar (χ₁ * χ₂⁻¹) b : ℂ) * ((finMod b : ℝ) : ℂ) ^ (2 * s) ∂finiteIdeleMeasure K := by
    rw [← integral_prod_mul, globalZeta, integral_ideleMeasure]
    congr 1
    funext p
    have h1 := val_symm_fst p
    have h2 := val_symm_snd p
    simp only [slice, schwartzBruhatTensor2, infPart_slice, finPart_slice, h1, h2]
    rw [toIdele_eq_finChar_mul_infChar, toInfinite_symm, toFinite_symm]
    change _ * _ * (modPow _ (2 * s)) = _
    rw [modPow_eq, toInfinite_symm, toFinite_symm, Circle.coe_mul]
    ring
  rw [godementSection, hZ, archSection, finSection, toIdele_eq_finChar_mul_infChar, modPow_eq,
    toInfinite_detI, toFinite_detI, Circle.coe_mul]
  ring

theorem finSlice_mem {Φ : (Fin 2 → FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hΦ : Φ ∈ finiteSchwartzBruhat2 K) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (fun b : FiniteAdeleRing (𝓞 K) K ↦
      Φ (![0, b] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) ∈
        finiteSchwartzBruhat K := by
  obtain ⟨hlc, hcs⟩ := (mem_finiteSchwartzBruhat2 K).mp (comp_vecMul_mem_finiteSchwartzBruhat2 g hΦ)
  have hcl : Topology.IsClosedEmbedding (fun v : FiniteAdeleRing (𝓞 K) K ↦ ![0, v]) :=
    Function.LeftInverse.isClosedEmbedding (f := fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦ x 1)
      (fun v ↦ rfl) (continuous_apply 1)
      (continuous_pi (Fin.forall_fin_two.mpr ⟨continuous_const, continuous_id⟩))
  exact ⟨hlc.comp_continuous hcl.continuous, hcs.comp_isClosedEmbedding hcl⟩

theorem finMod_eq (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : finMod b = finiteModule (ofFinite b) := by
  simp only [finMod, finiteModule, ofFinite_val_snd]

theorem continuous_finMod : Continuous (finMod (K := K)) :=
  (continuous_finiteModule.comp continuous_ofFinite).congr fun b ↦ (finMod_eq b).symm

theorem integrable_norm_finIntegrand {Φ : (Fin 2 → FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hΦ : Φ ∈ finiteSchwartzBruhat2 K) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) {σ : ℝ}
    (hσ : 1 < σ) :
    Integrable (fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      ‖Φ (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)))‖ * finMod b ^ σ)
      (finiteIdeleMeasure K) := by
  set h : FiniteAdeleRing (𝓞 K) K → ℂ := fun b ↦
    Φ (![0, b] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) with hh
  have hmem : h ∈ finiteSchwartzBruhat K := finSlice_mem hΦ g
  obtain ⟨M, hM⟩ := hmem.1.continuous.bounded_above_of_compact_support hmem.2
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hmem.2
  have hcont : Continuous fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ ‖h b‖ * finMod b ^ σ :=
    (hmem.1.continuous.comp Units.continuous_val).norm.mul
      (continuous_finMod.rpow_const fun b ↦ Or.inl (finMod_pos b).ne')
  refine ((integrable_finiteZetaBound L hσ).const_mul (max M 0)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun b ↦ ?_)
  have hpow : 0 ≤ finMod b ^ σ := (Real.rpow_pos_of_pos (finMod_pos b) σ).le
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hpow)]
  by_cases hb : (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L
  · have hfz : finiteZetaBound L σ b = finMod b ^ σ := by
      rw [finiteZetaBound, if_pos hb, finMod_eq]
    rw [hfz]
    exact mul_le_mul_of_nonneg_right ((hM _).trans (le_max_left _ _)) hpow
  · have h0 : h b = 0 := by
      by_contra hne
      exact hb (hL (subset_tsupport h hne))
    change ‖h b‖ * _ ≤ _
    rw [h0, norm_zero, zero_mul]
    exact mul_nonneg (le_max_right _ _) (finiteZetaBound_nonneg _ _ _)

def toMixedGL (g : GL (Fin 2) (InfiniteAdeleRing K)) : GL (Fin 2) (mixedSpace K) :=
  Matrix.GeneralLinearGroup.map
    (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K →+* mixedSpace K) g

def archSliceMap (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    mixedSpace K →L[ℝ] (Fin 2 → mixedSpace K) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u j ↦ u * (toMixedGL g : Matrix (Fin 2) (Fin 2) (mixedSpace K)) 1 j
      map_add' := fun u v ↦ by funext j; simp [add_mul]
      map_smul' := fun c u ↦ by funext j; simp }

theorem archSliceMap_apply (g : GL (Fin 2) (InfiniteAdeleRing K)) (a : InfiniteAdeleRing K) :
    archSliceMap g (homeomorphMixedSpace K a) =
      infVec (![0, a] ᵥ* (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) := by
  funext j
  simp only [archSliceMap, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    infVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, toMixedGL,
    Matrix.GeneralLinearGroup.map_apply, homeomorphMixedSpace_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_mul, zero_add]
  exact (map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace K) a _).symm

theorem norm_le_archSliceMap (g : GL (Fin 2) (InfiniteAdeleRing K)) (u : mixedSpace K) :
    ‖u‖ ≤ (‖((toMixedGL g)⁻¹ : GL (Fin 2) (mixedSpace K)) 0 1‖ +
      ‖((toMixedGL g)⁻¹ : GL (Fin 2) (mixedSpace K)) 1 1‖) * (1 + ‖archSliceMap g u‖) ^ 1 := by
  set N := ((toMixedGL g)⁻¹ : GL (Fin 2) (mixedSpace K))
  set w := archSliceMap g u
  have hw : w = ![0, u] ᵥ* (toMixedGL g : Matrix (Fin 2) (Fin 2) (mixedSpace K)) := by
    funext j
    simp [w, archSliceMap, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hu : u = w 0 * N 0 1 + w 1 * N 1 1 := by
    have : ![0, u] = w ᵥ* (N : Matrix (Fin 2) (Fin 2) (mixedSpace K)) := by
      rw [hw, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.vecMul_one]
    have := congrFun this 1
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have h0 : ‖w 0‖ ≤ ‖w‖ := norm_le_pi_norm w 0
  have h1 : ‖w 1‖ ≤ ‖w‖ := norm_le_pi_norm w 1
  rw [pow_one]
  calc ‖u‖ = ‖w 0 * N 0 1 + w 1 * N 1 1‖ := by rw [← hu]
    _ ≤ ‖w 0‖ * ‖N 0 1‖ + ‖w 1‖ * ‖N 1 1‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖w‖ * ‖N 0 1‖ + ‖w‖ * ‖N 1 1‖ :=
        add_le_add (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    _ ≤ (‖N 0 1‖ + ‖N 1 1‖) * (1 + ‖w‖) := by
        have := norm_nonneg w
        have := norm_nonneg (N 0 1)
        have := norm_nonneg (N 1 1)
        nlinarith

def archSlice (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.compCLM ℂ (archSliceMap g).hasTemperateGrowth ⟨1, _, norm_le_archSliceMap g⟩ φ

theorem archSlice_apply (φ : 𝓢(Fin 2 → mixedSpace K, ℂ)) (g : GL (Fin 2) (InfiniteAdeleRing K))
    (a : InfiniteAdeleRing K) :
    archSlice φ g (homeomorphMixedSpace K a) =
      φ (infVec (![0, a] ᵥ* (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)))) := by
  rw [archSlice, SchwartzMap.compCLM_apply, Function.comp_apply, archSliceMap_apply]

end

end GroundTheory.Automorphic.GodementSection
