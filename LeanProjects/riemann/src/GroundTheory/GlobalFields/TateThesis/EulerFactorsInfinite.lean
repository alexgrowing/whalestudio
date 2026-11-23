import Mathlib
import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import GroundTheory.GlobalFields.TateThesis.TraceFourier
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
import GroundTheory.GlobalFields.Adele.IntegersLattice

open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace

namespace GroundTheory.Global

noncomputable section

theorem hasTemperateGrowth_finsetProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x ↦ ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact HasTemperateGrowth.const (1 : ℂ)
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem ofReal_finsetProd_cpow {ι : Type*} (t : Finset ι) {r : ι → ℝ} (hr : ∀ i ∈ t, 0 ≤ r i)
    (s : ℂ) : ((∏ i ∈ t, r i : ℝ) : ℂ) ^ s = ∏ i ∈ t, ((r i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ofReal_mul,
      mul_cpow_ofReal_nonneg (hr a (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)]

variable {K : Type*} [Field K] [NumberField K]

theorem norm_mixedToEuclidean_sq (x : mixedSpace K) :
    ‖mixedToEuclidean K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change ⟪(euclidean.toMixed K).symm (mapComplexCoord K sqrtTwoSMulComplex x),
    (euclidean.toMixed K).symm (mapComplexCoord K sqrtTwoSMulComplex x)⟫ = _
  rw [inner_toMixed_symm, mapComplexCoord_apply, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun w _ ↦ by ring
  · refine Finset.sum_congr rfl fun w _ ↦ ?_
    dsimp only
    rw [sqrtTwoSMulComplex_apply, Complex.real_smul, map_mul, conj_ofReal,
      show ((√2 : ℝ) : ℂ) * conj (x.2 w) * (((√2 : ℝ) : ℂ) * x.2 w) =
        (((√2 : ℝ) ^ 2 : ℝ) : ℂ) * (conj (x.2 w) * x.2 w) by push_cast; ring,
      Real.sq_sqrt (by norm_num), Complex.conj_mul']
    norm_cast

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def infinitePoly (x : mixedSpace K) : ℂ :=
  (∏ w : {w // IsReal w}, ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs) *
    ∏ w : {w // IsComplex w},
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^ (χ.infiniteWeight w).natAbs

theorem hasTemperateGrowth_infinitePoly : χ.infinitePoly.HasTemperateGrowth := by
  have h1 : ∀ w : {w // IsReal w}, (fun x : mixedSpace K ↦
      ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs).HasTemperateGrowth := fun w ↦ by
    have h := (((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w // IsReal w} → ℝ)
        ({w // IsComplex w} → ℂ))) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
    exact h
  have h2 : ∀ w : {w // IsComplex w}, (fun x : mixedSpace K ↦
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^
        (χ.infiniteWeight w).natAbs).HasTemperateGrowth := by
    intro w
    by_cases hw : 0 < χ.infiniteWeight w
    · simp only [if_pos hw]
      have h := (((Complex.conjCLE.toContinuousLinearMap.comp ((ContinuousLinearMap.proj w :
        ({w // IsComplex w} → ℂ) →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ({w // IsReal w} → ℝ)
          ({w // IsComplex w} → ℂ))) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
      exact h
    · simp only [if_neg hw]
      have h := ((((ContinuousLinearMap.proj w : ({w // IsComplex w} → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.snd ℝ ({w // IsReal w} → ℝ)
          ({w // IsComplex w} → ℂ)) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
      exact h
  exact (hasTemperateGrowth_finsetProd _ fun w _ ↦ h1 w).mul
    (hasTemperateGrowth_finsetProd _ fun w _ ↦ h2 w)

def infiniteSchwartz : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ χ.infinitePoly
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K)
      (gaussianSchwartz (euclidean.mixedSpace K)))

theorem infiniteSchwartz_apply (x : mixedSpace K) :
    χ.infiniteSchwartz x = χ.infinitePoly x *
      ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [infiniteSchwartz, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth_infinitePoly,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]

theorem infiniteSchwartz_homeomorphMixedSpace (x : InfiniteAdeleRing K) :
    χ.infiniteSchwartz (homeomorphMixedSpace K x) = ∏ w, χ.infiniteTest w (x w) := by
  rw [infiniteSchwartz_apply, prod_eq_prod_mul_prod, homeomorphMixedSpace_apply,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [infinitePoly, infiniteTest, Finset.prod_mul_distrib]
  have hr : ∀ w : {w // IsReal w}, (if 0 < χ.infiniteWeight w.1 then
      conj (extensionEmbedding w.1 (x w.1)) else extensionEmbedding w.1 (x w.1)) =
        ((extensionEmbeddingOfIsReal w.2 (x w.1) : ℝ) : ℂ) := fun w ↦ by
    rw [extensionEmbeddingOfIsReal_apply]
    split_ifs
    · rw [← extensionEmbeddingOfIsReal_apply w.2, conj_ofReal]
    · rfl
  have hnr : ∀ w : {w // IsReal w}, (extensionEmbeddingOfIsReal w.2 (x w.1)) ^ 2 = ‖x w.1‖ ^ 2 :=
    fun w ↦ by
      rw [← (isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _),
        Real.norm_eq_abs, sq_abs]
  have hnc : ∀ w : {w // IsComplex w}, ‖extensionEmbedding w.1 (x w.1)‖ = ‖x w.1‖ := fun w ↦
    (isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _
  simp only [hr, hnr, hnc, mult_isReal, mult_isComplex]
  have hexp : ((Real.exp (-π * (∑ w : {w // IsReal w}, ‖x w.1‖ ^ 2 +
      2 * ∑ w : {w // IsComplex w}, ‖x w.1‖ ^ 2)) : ℝ) : ℂ) =
      (∏ w : {w // IsReal w}, ((Real.exp (-(π * ((1 : ℕ) : ℝ) * ‖x w.1‖ ^ 2)) : ℝ) : ℂ)) *
        ∏ w : {w // IsComplex w}, ((Real.exp (-(π * ((2 : ℕ) : ℝ) * ‖x w.1‖ ^ 2)) : ℝ) : ℂ) := by
    rw [← ofReal_prod, ← ofReal_prod, ← ofReal_mul, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
    congr 2
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun w _ ↦ by push_cast; ring
  rw [hexp]
  ring

theorem toIdele_ofInfinite (a : (InfiniteAdeleRing K)ˣ) :
    χ.toIdele (IdeleGroup.ofInfinite a) =
      ∏ w, χ.infiniteComponent w (IdeleGroup.infiniteComponent w a) := by
  have ha : a = ∏ w, Units.map (IdeleGroup.infiniteAdeleSingle w) (IdeleGroup.infiniteComponent w a) := by
    ext1
    rw [Units.coe_prod]
    simp only [Units.coe_map, IdeleGroup.coe_infiniteComponent]
    exact (Finset.univ_prod_mulSingle (fun w ↦ (a : InfiniteAdeleRing K) w)).symm
  conv_lhs => rw [ha]
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun w _ ↦ by
    rw [IdeleGroup.ofInfinite_map_infiniteAdeleSingle]
    rfl

theorem integral_infiniteSchwartz {s : ℂ} (hs : 0 < s.re) :
    ∫ a : (InfiniteAdeleRing K)ˣ, χ.infiniteSchwartz (homeomorphMixedSpace K a) *
      (χ.toIdele (IdeleGroup.ofInfinite a) : ℂ) *
        ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure K =
      ∏ w, infiniteConst w * χ.infiniteGamma w s := by
  have he : MeasurableEmbedding (infiniteUnitsEquiv K).symm :=
    (infiniteUnitsEquiv K).symm.toHomeomorph.measurableEmbedding
  rw [infiniteIdeleMeasure, he.integral_map]
  have hpt : ∀ y : Π w : InfinitePlace K, (w.Completion)ˣ,
      χ.infiniteSchwartz (homeomorphMixedSpace K ((infiniteUnitsEquiv K).symm y)) *
        (χ.toIdele (IdeleGroup.ofInfinite ((infiniteUnitsEquiv K).symm y)) : ℂ) *
        ((∏ w, ‖(((infiniteUnitsEquiv K).symm y : (InfiniteAdeleRing K)ˣ) :
          InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s =
      ∏ w, χ.infiniteTest w (y w) * χ.infiniteComponent w (y w) *
        ((‖(y w : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s := by
    intro y
    have hy : ∀ w, (((infiniteUnitsEquiv K).symm y : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) w = (y w : w.Completion) := fun w ↦ rfl
    have hc : ∀ w, IdeleGroup.infiniteComponent w ((infiniteUnitsEquiv K).symm y) = y w :=
      fun w ↦ Units.ext rfl
    rw [infiniteSchwartz_homeomorphMixedSpace, toIdele_ofInfinite,
      ofReal_finsetProd_cpow _ (fun w _ ↦ by positivity)]
    have hcp : ((∏ w, χ.infiniteComponent w (y w) : Circle) : ℂ) =
        ∏ w, (χ.infiniteComponent w (y w) : ℂ) :=
      map_prod Circle.coeHom (fun w ↦ χ.infiniteComponent w (y w)) Finset.univ
    simp only [hy, hc, hcp, Finset.prod_mul_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hfub := integral_fintype_prod_eq_prod (μ := fun w : InfinitePlace K ↦ infinitePlaceUnitsMeasure w)
    (fun w (u : (w.Completion)ˣ) ↦ χ.infiniteTest w u * (χ.infiniteComponent w u : ℂ) *
      ((‖(u : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s)
  exact hfub.trans (Finset.prod_congr rfl fun w _ ↦ χ.integral_infiniteTest w hs)

end HeckeCharacter

end

end GroundTheory.Global
