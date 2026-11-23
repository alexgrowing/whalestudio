import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphPiece
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.VolumeLtHausdorffUnitBallTwenty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace AreaGraphPiece

variable {k m : ℕ}

def pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => u i) (fun i => w i))

def firstPart (p : EuclideanSpace ℝ (Fin k ⊕ Fin m)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => p (Sum.inl i))

theorem realGraphPt_eq (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : realGraphPt F x = pairPt x (F x) := rfl

theorem firstPart_pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    firstPart (pairPt u w) = u := by
  ext i
  simp [firstPart, pairPt]

theorem pairPt_add (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w + pairPt u' w' = pairPt (u + u') (w + w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem pairPt_sub (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w - pairPt u' w' = pairPt (u - u') (w - w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem pairPt_smul (c : ℝ) (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    c • pairPt u w = pairPt (c • u) (c • w) := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem inner_pairPt (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    ⟪pairPt u w, pairPt u' w'⟫ = ⟪u, u'⟫ + ⟪w, w'⟫ := by
  simp [pairPt, PiLp.inner_apply, Fintype.sum_sum_type]

theorem norm_pairPt_sq (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt u w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_pairPt]

theorem norm_le_norm_pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖u‖ ≤ ‖pairPt u w‖ := by
  have h := norm_pairPt_sq u w
  nlinarith [norm_nonneg u, norm_nonneg (pairPt u w), sq_nonneg ‖w‖]

theorem norm_pairPt_zero (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt (0 : EuclideanSpace ℝ (Fin k)) w‖ = ‖w‖ := by
  have h := norm_pairPt_sq (0 : EuclideanSpace ℝ (Fin k)) w
  rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

def graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k ⊕ Fin m) where
  toFun x := pairPt x (A x)
  map_add' x y := by rw [map_add, pairPt_add]
  map_smul' c x := by rw [map_smul, pairPt_smul]; rfl

theorem graphLin_apply (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : graphLin A x = pairPt x (A x) := rfl

theorem adjoint_graphLin_comp (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    LinearMap.adjoint (graphLin A) ∘ₗ graphLin A =
      (1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
        LinearMap.adjoint (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘ₗ
          (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.add_apply, inner_add_left,
    Module.End.one_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_left, graphLin_apply,
    graphLin_apply, inner_pairPt]
  rfl

theorem normDet_graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (graphLin A).normDet =
      graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  unfold graphJac
  rw [← adjoint_graphLin_comp, ← LinearMap.normDet_sq (graphLin A)]
  push_cast
  exact (Real.sqrt_sq (LinearMap.normDet_nonneg _)).symm

end AreaGraphPiece

open AreaGraphPiece in

theorem AreaGraphPiece.proof : AreaGraphPiece.Statement := by
  intro k m F A δ t hδ hF
  set L := graphLin A with hLdef
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) ≤ δ := δ.2

  have hsub : ∀ x y, realGraphPt F x - realGraphPt F y - L (x - y) =
      pairPt (0 : EuclideanSpace ℝ (Fin k)) (F x - F y - A (x - y)) := by
    intro x y
    rw [realGraphPt_eq, realGraphPt_eq, hLdef, graphLin_apply, pairPt_sub, pairPt_sub]
    simp
  have hL : ∀ v, ‖v‖ ≤ ‖L v‖ := fun v => norm_le_norm_pairPt v (A v)
  have hclose : ∀ x ∈ t, ∀ y ∈ t,
      |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖| ≤ δ * ‖L (x - y)‖ := by
    intro x hx y hy
    calc |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖|
        ≤ ‖realGraphPt F x - realGraphPt F y - L (x - y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖F x - F y - A (x - y)‖ := by rw [hsub, norm_pairPt_zero]
      _ ≤ δ * ‖x - y‖ := hF x hx y hy
      _ ≤ δ * ‖L (x - y)‖ := mul_le_mul_of_nonneg_left (hL _) hδ0

  have himG : realGraphPt F '' t = (fun p => realGraphPt F (firstPart p)) '' (L '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hLdef, graphLin_apply, firstPart_pairPt]
  have hlipG : LipschitzOnWith (1 + δ) (fun p => realGraphPt F (firstPart p)) (L '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [hLdef, graphLin_apply, firstPart_pairPt, dist_eq_norm]
    rw [← graphLin_apply, ← graphLin_apply, ← map_sub, ← hLdef]
    have h := (abs_le.1 (hclose x hx y hy)).2
    push_cast
    linarith

  have himL : L '' t = (fun p => L (firstPart p)) '' (realGraphPt F '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [realGraphPt_eq, firstPart_pairPt]
  have hlipL : LipschitzOnWith (1 - δ)⁻¹ (fun p => L (firstPart p)) (realGraphPt F '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [realGraphPt_eq, firstPart_pairPt, dist_eq_norm]
    rw [← realGraphPt_eq, ← realGraphPt_eq, ← map_sub]
    have h := (abs_le.1 (hclose x hx y hy)).1
    rw [NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one, inv_mul_eq_div,
      le_div_iff₀ (by linarith)]
    nlinarith

  have harea : μH[(k : ℝ)] (L '' t) =
      ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
        μH[(k : ℝ)] t := by
    have h := LinearMap.hausdorffMeasure_image L t
    rw [finrank_euclideanSpace_fin] at h
    rw [h, hLdef, normDet_graphLin]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · calc μH[(k : ℝ)] (realGraphPt F '' t)
        = μH[(k : ℝ)] ((fun p => realGraphPt F (firstPart p)) '' (L '' t)) := by rw [← himG]
      _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (L '' t) :=
          hlipG.hausdorffMeasure_image_le hk
      _ = _ := by rw [harea, ENNReal.rpow_natCast, mul_assoc]
  · have hle : μH[(k : ℝ)] (L '' t) ≤
        (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t) := by
      calc μH[(k : ℝ)] (L '' t)
          = μH[(k : ℝ)] ((fun p => L (firstPart p)) '' (realGraphPt F '' t)) := by rw [← himL]
        _ ≤ (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (realGraphPt F '' t) :=
            hlipL.hausdorffMeasure_image_le hk
        _ = _ := by rw [ENNReal.rpow_natCast]
    have hne : (1 - δ : ℝ≥0) ≠ 0 := (tsub_pos_of_lt hδ).ne'
    calc ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
            μH[(k : ℝ)] t
        = ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (L '' t) := by rw [harea, mul_assoc]
      _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ((((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t)) := by gcongr
      _ = μH[(k : ℝ)] (realGraphPt F '' t) := by
          rw [← mul_assoc, ← mul_pow, ← ENNReal.coe_mul, mul_inv_cancel₀ hne, ENNReal.coe_one,
            one_pow, one_mul]

end

end GroundTheory.Heights₂.Heights
