import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub

noncomputable section

open MeasureTheory Matrix
open PositivityTheory.RgTw (Mat G)

namespace PositivityTheory.Rg.BcB.CG

namespace PVC

variable {n : ℕ}

theorem mem_nilrad {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ nilrad W₁ W₂ ↔ (∀ y, X *ᵥ y ∈ W₂) ∧ (∀ y ∈ W₂, X *ᵥ y ∈ W₁) ∧ ∀ y ∈ W₁, X *ᵥ y = 0 := Iff.rfl

theorem nil_mul_mem {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ nilrad W₁ W₂) (hY : Y ∈ nilrad W₁ W₂) : X * Y ∈ nilrad W₁ W₂ := by
  rw [mem_nilrad] at hX hY ⊢
  refine ⟨fun y => ?_, fun y _ => ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec]; exact hX.1 _
  · rw [← Matrix.mulVec_mulVec]; exact hX.2.1 _ (hY.1 y)
  · rw [← Matrix.mulVec_mulVec, hY.2.2 y hy, Matrix.mulVec_zero]

theorem nil_cube {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ nilrad W₁ W₂) : X * X * X = 0 := by
  rw [mem_nilrad] at hX
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  exact hX.2.2 _ (hX.2.1 _ (hX.1 v))

def uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) : G n where
  val := 1 + X.1
  inv := 1 - X.1 + X.1 * X.1
  val_inv := by
    calc (1 + X.1) * (1 - X.1 + X.1 * X.1) = 1 + X.1 * X.1 * X.1 := by noncomm_ring
      _ = 1 := by rw [nil_cube X.2, add_zero]
  inv_val := by
    calc (1 - X.1 + X.1 * X.1) * (1 + X.1) = 1 + X.1 * X.1 * X.1 := by noncomm_ring
      _ = 1 := by rw [nil_cube X.2, add_zero]

def nilSub (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : Subgroup (G n) where
  carrier := PositivityTheory.RgBcC.nilSet W₁ W₂
  one_mem' := by
    show ((1 : G n).val - 1) ∈ nilrad W₁ W₂
    rw [Units.val_one, sub_self]; exact zero_mem _
  mul_mem' := by
    intro a b ha hb
    have ha' : a.val - 1 ∈ nilrad W₁ W₂ := ha
    have hb' : b.val - 1 ∈ nilrad W₁ W₂ := hb
    show (a * b).val - 1 ∈ nilrad W₁ W₂
    have e : (a * b).val - 1 = (a.val - 1) + (b.val - 1) + (a.val - 1) * (b.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e]; exact add_mem (add_mem ha' hb') (nil_mul_mem ha' hb')
  inv_mem' := by
    intro a ha
    have ha' : a.val - 1 ∈ nilrad W₁ W₂ := ha
    show (a⁻¹ : G n).val - 1 ∈ nilrad W₁ W₂
    have h3 := nil_cube ha'
    have hinv : (a⁻¹ : G n).val = 1 - (a.val - 1) + (a.val - 1) * (a.val - 1) := by
      have e : a.val * (1 - (a.val - 1) + (a.val - 1) * (a.val - 1)) = 1 := by
        calc a.val * (1 - (a.val - 1) + (a.val - 1) * (a.val - 1))
            = 1 + (a.val - 1) * (a.val - 1) * (a.val - 1) := by noncomm_ring
          _ = 1 := by rw [h3, add_zero]
      calc (a⁻¹ : G n).val = (a⁻¹ : G n).val * (a.val * (1 - (a.val - 1) + (a.val - 1) * (a.val - 1))) := by
            rw [e, mul_one]
        _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [hinv]
    have e2 : 1 - (a.val - 1) + (a.val - 1) * (a.val - 1) - 1 = -(a.val - 1) + (a.val - 1) * (a.val - 1) := by
      abel
    rw [e2]; exact add_mem (neg_mem ha') (nil_mul_mem ha' ha')

def eN (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) : nilSub W₁ W₂ :=
  ⟨uOf X, show (1 + X.1) - 1 ∈ nilrad W₁ W₂ by rw [add_sub_cancel_left]; exact X.2⟩

def eH (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : nilrad W₁ W₂ ≃ₜ nilSub W₁ W₂ where
  toFun := eN W₁ W₂
  invFun w := ⟨w.1.val - 1, w.2⟩
  left_inv X := Subtype.ext (show 1 + X.1 - 1 = X.1 by rw [add_sub_cancel_left])
  right_inv w := Subtype.ext (Units.ext (show 1 + (w.1.val - 1) = w.1.val by rw [add_sub_cancel]))
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · show Continuous fun X : nilrad W₁ W₂ => 1 + X.1
      fun_prop
    · show Continuous fun X : nilrad W₁ W₂ => 1 - X.1 + X.1 * X.1
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (Units.continuous_val.comp continuous_subtype_val).sub continuous_const

theorem eH_val {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) :
    ((eH W₁ W₂ X : nilSub W₁ W₂) : G n).val = 1 + X.1 := rfl

section Haar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}

theorem map_aff [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
    [ν.IsAddHaarMeasure] (Y : nilrad W₁ W₂) :
    Measure.map (fun X : nilrad W₁ W₂ =>
      (⟨Y.1 + (X.1 + Y.1 * X.1), add_mem Y.2 (add_mem X.2 (nil_mul_mem Y.2 X.2))⟩ : nilrad W₁ W₂)) ν = ν := by
  have : FiniteDimensional ℝ (nilrad W₁ W₂) := Module.Finite.trans ℂ (nilrad W₁ W₂)
  let ℓ : nilrad W₁ W₂ →ₗ[ℝ] nilrad W₁ W₂ :=
    { toFun := fun X => ⟨Y.1 * X.1, nil_mul_mem Y.2 X.2⟩
      map_add' := fun X X' => Subtype.ext (by simp [Matrix.mul_add])
      map_smul' := fun r X => Subtype.ext (by simp) }
  have hnil : IsNilpotent ℓ := by
    refine ⟨3, LinearMap.ext fun X => Subtype.ext ?_⟩
    rw [pow_three]
    show Y.1 * (Y.1 * (Y.1 * X.1)) = 0
    rw [← mul_assoc, ← mul_assoc, nil_cube Y.2, zero_mul]
  have hdet : LinearMap.det (1 + ℓ) = 1 := by
    have h := LinearMap.eval_charpoly (-ℓ) (1 : ℝ)
    rw [IsNilpotent.charpoly_eq_X_pow_finrank hnil.neg, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
      map_one, sub_neg_eq_add] at h
    exact h.symm
  have hLc : Continuous ((1 + ℓ : nilrad W₁ W₂ →ₗ[ℝ] nilrad W₁ W₂) : nilrad W₁ W₂ → nilrad W₁ W₂) := by
    show Continuous fun X : nilrad W₁ W₂ =>
      (⟨X.1 + Y.1 * X.1, add_mem X.2 (nil_mul_mem Y.2 X.2)⟩ : nilrad W₁ W₂)
    exact Continuous.subtype_mk (by fun_prop) _
  have hA : (fun X : nilrad W₁ W₂ =>
      (⟨Y.1 + (X.1 + Y.1 * X.1), add_mem Y.2 (add_mem X.2 (nil_mul_mem Y.2 X.2))⟩ : nilrad W₁ W₂)) =
      (fun X => Y + X) ∘ ((1 + ℓ : nilrad W₁ W₂ →ₗ[ℝ] nilrad W₁ W₂) : nilrad W₁ W₂ → nilrad W₁ W₂) := by
    funext X; rfl
  have key := @MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (nilrad W₁ W₂) _ _ _
    (by exact ‹BorelSpace (nilrad W₁ W₂)›) _ ν (by exact ‹ν.IsAddHaarMeasure›) (1 + ℓ)
    (by rw [hdet]; exact one_ne_zero)
  rw [hA, ← Measure.map_map (measurable_const_add Y) hLc.measurable, key, hdet, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul, map_add_left_eq_self]

theorem haar_map [MeasurableSpace (G n)] [BorelSpace (G n)] [MeasurableSpace (nilrad W₁ W₂)]
    [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] :
    (Measure.map (eH W₁ W₂) ν).IsHaarMeasure where
  toIsFiniteMeasureOnCompacts := ⟨fun K hK => by
    have h := (eH W₁ W₂).toMeasurableEquiv.map_apply (μ := ν) K
    rw [Homeomorph.toMeasurableEquiv_coe] at h
    rw [h]
    exact ((eH W₁ W₂).isCompact_preimage.2 hK).measure_lt_top⟩
  toIsOpenPosMeasure := (eH W₁ W₂).continuous.isOpenPosMeasure_map (eH W₁ W₂).surjective
  toIsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    set Y := (eH W₁ W₂).symm g
    have hg : g = eH W₁ W₂ Y := by simp [Y]
    have hcomp : (fun x => g * x) ∘ (eH W₁ W₂) = (eH W₁ W₂) ∘ (fun X : nilrad W₁ W₂ =>
        (⟨Y.1 + (X.1 + Y.1 * X.1), add_mem Y.2 (add_mem X.2 (nil_mul_mem Y.2 X.2))⟩ : nilrad W₁ W₂)) := by
      funext X
      refine Subtype.ext (Units.ext ?_)
      show (g : G n).val * (1 + X.1) = 1 + (Y.1 + (X.1 + Y.1 * X.1))
      rw [hg, eH_val]
      noncomm_ring
    rw [Measure.map_map (continuous_const_mul g).measurable (eH W₁ W₂).continuous.measurable, hcomp,
      ← Measure.map_map (eH W₁ W₂).continuous.measurable (by fun_prop), map_aff]

end Haar

theorem tr_mul_comm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (A B : V →L[ℂ] V) :
    LinearMap.trace ℂ V ((A * B : V →L[ℂ] V) : V →ₗ[ℂ] V) = LinearMap.trace ℂ V ((B * A : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
  have h : ∀ X Y : V →L[ℂ] V, ((X * Y : V →L[ℂ] V) : V →ₗ[ℂ] V) = (X : V →ₗ[ℂ] V) * (Y : V →ₗ[ℂ] V) :=
    fun _ _ => rfl
  rw [h, h, LinearMap.trace_mul_comm]

end PVC

open PVC in
theorem vcBridge : VCBridge := by
  intro n _ _ μ M Tθ k val T hT hM hVC
  obtain ⟨m, c, w, g, ks, hks, hsum, -⟩ := hM
  have hG : ∀ x : G n, x.val ∈ PositivityTheory.RgBcC.GLs n := fun x => (Matrix.isUnits_det_units x).ne_zero
  refine ⟨fun u d hθ => ?_, fun d W₁ W₂ hne hle hp1 hp2 u hu _ _ ν _ => ?_⟩
  · have hs : star u.val = (u⁻¹ : G n).val := by
      have h := congrArg Units.val hθ
      rw [thetaR_val] at h
      rw [← h]
      ext i j
      simp [Matrix.star_apply]
    let U : Matrix.unitaryGroup (Fin n) ℂ :=
      ⟨u.val, Matrix.mem_unitaryGroup_iff'.2 (by rw [hs]; exact u.inv_mul)⟩
    have hUi : ((U⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) = (u⁻¹ : G n).val := by
      rw [← hs]; rfl
    have hval : (PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) u d).val =
        ((U⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) * d.val * (U : Mat n) := by
      rw [PositivityTheory.Rg.Tf.Loc.twConj, hθ, hUi, Units.val_mul, Units.val_mul]
    have hkey : k (PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) u d).val =
        M.ρ U⁻¹ * k d.val * M.ρ U := by
      rw [hsum _ (hG (PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) u d)), hsum _ (hG d), hval,
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hks i).2.2.2.1 _ (hG d) U⁻¹ U]
      simp only [mul_smul_comm, smul_mul_assoc]
    have e1 : M.ρ U⁻¹ * k d.val * M.ρ U * Tθ = M.ρ U⁻¹ * (k d.val * Tθ * M.ρ U) := by
      rw [mul_assoc _ (M.ρ U), ← hT U]; simp only [mul_assoc]
    have e2 : k d.val * Tθ * M.ρ U * M.ρ U⁻¹ = k d.val * Tθ := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    simp only [PositivityTheory.RgBcC.phiOf]
    rw [hkey, e1, tr_mul_comm, e2]
  · have hImg : ∀ W : Submodule ℂ (Fin n → ℂ), (fun v => d.val *ᵥ v) '' PositivityTheory.RgBcC.perp W =
        ((perpD (starRingEnd ℂ) d W : Submodule ℂ (Fin n → ℂ)) : Set (Fin n → ℂ)) := by
      intro W
      have h1 : (⇑(Matrix.toLin' d.val)) = fun v => d.val *ᵥ v := funext fun v => Matrix.toLin'_apply _ _
      have h2 : ((PositivityTheory.Rg.BcB.perp (starRingEnd ℂ) W : Submodule ℂ (Fin n → ℂ)) : Set (Fin n → ℂ)) =
          PositivityTheory.RgBcC.perp W := by
        ext v; exact Iff.rfl
      rw [perpD, PositivityTheory.Rg.BcB.img, Submodule.map_coe, h1, h2]
    have hc1 : (fun v => d.val *ᵥ v) '' PositivityTheory.RgBcC.perp W₂ = (W₁ : Set (Fin n → ℂ)) := by rw [hImg, hp2]
    have hc2 : (fun v => d.val *ᵥ v) '' PositivityTheory.RgBcC.perp W₁ = (W₂ : Set (Fin n → ℂ)) := by rw [hImg, hp1]
    have := haar_map (W₁ := W₁) (W₂ := W₂) ν
    have hz := hVC d W₁ W₂ hle hne hc1 hc2 (nilSub W₁ W₂) rfl (Measure.map (eH W₁ W₂) ν)
    have hint : ∫ w : nilSub W₁ W₂, PositivityTheory.RgBcC.phiOf M Tθ k (w * d) ∂(Measure.map (eH W₁ W₂) ν) =
        ∫ X, PositivityTheory.RgBcC.phiOf M Tθ k ((eH W₁ W₂ X : G n) * d) ∂ν := by
      have := integral_map_equiv (μ := ν) (eH W₁ W₂).toMeasurableEquiv
        (fun w : nilSub W₁ W₂ => PositivityTheory.RgBcC.phiOf M Tθ k (w * d))
      rw [Homeomorph.toMeasurableEquiv_coe] at this
      exact this
    have hu' : ∀ X, ((eH W₁ W₂ X : nilSub W₁ W₂) : G n) = u X := fun X => Units.ext (by rw [hu X]; rfl)
    calc ∫ X, PositivityTheory.RgBcC.phiOf M Tθ k (u X * d) ∂ν
        = ∫ X, PositivityTheory.RgBcC.phiOf M Tθ k ((eH W₁ W₂ X : G n) * d) ∂ν := by simp_rw [hu']
      _ = ∫ w : nilSub W₁ W₂, PositivityTheory.RgBcC.phiOf M Tθ k (w * d) ∂(Measure.map (eH W₁ W₂) ν) := hint.symm
      _ = 0 := hz

end PositivityTheory.Rg.BcB.CG

end
