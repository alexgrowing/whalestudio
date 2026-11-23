import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace WeightInverseContinuity

theorem bil_bound {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (B : V →ₗ[ℝ] V →ₗ[ℝ] W) :
    ∃ K, 0 ≤ K ∧ ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖ := by
  let B' : V →ₗ[ℝ] (V →L[ℝ] W) :=
    (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] W) ≃ₗ[ℝ] (V →L[ℝ] W)).toLinearMap ∘ₗ B
  let T := LinearMap.toContinuousLinearMap B'
  refine ⟨‖T‖, norm_nonneg _, fun x y => ?_⟩
  have e : B x y = T x y := rfl
  rw [e]
  exact ((T x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _))

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem norm_mulL (A B : Lie E a) :
    ‖(toL (Matrix.of A * Matrix.of B) : Lie E a)‖ ≤ a * ‖A‖ * ‖B‖ := by
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  have hB : 0 ≤ ‖B‖ := norm_nonneg _
  have h0 : (0 : ℝ) ≤ a * ‖A‖ * ‖B‖ := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA) hB
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have e : (toL (Matrix.of A * Matrix.of B) : Lie E a) i j = ∑ k, A i k * B k j := by
    simp only [toL, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [e]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin a, ‖A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
        (mul_le_mul ((norm_le_pi_norm (A i) k).trans (norm_le_pi_norm A i))
          ((norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)) (norm_nonneg _) hA)
    _ = a * ‖A‖ * ‖B‖ := by simp [Finset.sum_const, Finset.card_univ, mul_assoc]

def invL (z : Lie E a) : Lie E a := toL (Matrix.of z)⁻¹

theorem invL_one : invL (oneL E a) = oneL E a := by
  simp only [invL, oneL, toL]
  show Matrix.of.symm ((1 : Matrix (Fin a) (Fin a) (Cinf E))⁻¹) = _
  simp

theorem continuousAt_invL : ContinuousAt (invL (E := E) (a := a)) (oneL E a) := by
  have h : ContinuousAt (fun z : Matrix (Fin a) (Fin a) (Cinf E) => z⁻¹) 1 :=
    continuousAt_matrix_inv _ (by
      rw [Matrix.det_one]
      exact NormedRing.inverse_continuousAt (1 : (Cinf E)ˣ))
  exact h

variable [IsTotallyComplex E]

theorem chart_inv (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ∃ h : GA E a, ∀ f : GA E a → ℂ, chart f g x = f h :=
  ⟨g * infGL E a (show IsUnit (Matrix.of x) from hx).unit, fun f => by
    rw [chart, dif_pos (show IsUnit (Matrix.of x) from hx)]⟩

theorem chart_one (f : GA E a → ℂ) (g : GA E a) : chart f g (oneL E a) = f g := by
  have e := chart_val f g 1
  rw [map_one, mul_one] at e
  exact e

theorem fderiv_chart {f : GA E a → ℂ} (hf : f ∈ Sm E a) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a)
    (Y : Lie E a) : fderiv ℝ (chart f g) x Y = chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Y)) f) g x := by
  rw [chart_lieD hf _ g hx]
  congr 1
  symm
  show (toL (Matrix.of x * ((Matrix.of x)⁻¹ * Matrix.of Y)) : Lie E a) = Y
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hx), Matrix.one_mul]
  rfl

theorem chart_sub_lieD (f : GA E a → ℂ) (A B : Lie E a) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (lieD A f) g x - chart (lieD B f) g x = chart (lieD (A - B) f) g x := by
  obtain ⟨h, hh⟩ := chart_inv g hx
  rw [hh, hh, hh]
  simp only [lieD, map_sub]

theorem normW {f : GA E a → ℂ} (hf : f ∈ Sm E a) {K : ℝ} (hK : 0 ≤ K) (g : GA E a) {x : Lie E a}
    (hx : x ∈ invSet E a) (hb : ∀ Z, ‖chart (lieD Z f) g x‖ ≤ K * ‖Z‖) :
    ‖fderiv ℝ (chart f g) x‖ ≤ K * (a * ‖invL x‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => ?_
  rw [fderiv_chart hf g hx]
  calc _ ≤ K * ‖(toL ((Matrix.of x)⁻¹ * Matrix.of Y) : Lie E a)‖ := hb _
    _ ≤ K * (a * ‖invL x‖ * ‖Y‖) := mul_le_mul_of_nonneg_left (norm_mulL (invL x) Y) hK
    _ = _ := by ring

theorem lipW {f : GA E a → ℂ} (hf : f ∈ Sm E a) {K Q r : ℝ} (hK : 0 ≤ K) (g : GA E a)
    (hr : Metric.ball (oneL E a) r ⊆ invSet E a) (hQ : ∀ x ∈ Metric.ball (oneL E a) r, ‖invL x‖ ≤ Q)
    (hb : ∀ Z, ∀ x ∈ Metric.ball (oneL E a) r, ‖chart (lieD Z f) g x‖ ≤ K * ‖Z‖)
    {x : Lie E a} (hx : x ∈ Metric.ball (oneL E a) r) :
    ‖chart f g x - f g‖ ≤ K * (a * Q) * ‖x - oneL E a‖ := by
  have h0 : oneL E a ∈ Metric.ball (oneL E a) r := Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hx)
  rw [← chart_one f g]
  exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (contDiffAt_chart hf g (hr hz)).differentiableAt (by simp))
    (fun z hz => (normW hf hK g (hr hz) fun Z => hb Z z hz).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hQ z hz) (Nat.cast_nonneg _)) hK)) h0 hx

theorem ddW {f : GA E a → ℂ} (hf : f ∈ Sm E a) {K K2 Q r : ℝ} (hK : 0 ≤ K) (hK2 : 0 ≤ K2) (g : GA E a)
    (hr : Metric.ball (oneL E a) r ⊆ invSet E a) (hQ : ∀ x ∈ Metric.ball (oneL E a) r, ‖invL x‖ ≤ Q)
    (hb1 : ∀ Z, ∀ x ∈ Metric.ball (oneL E a) r, ‖chart (lieD Z f) g x‖ ≤ K * ‖Z‖)
    (hb2 : ∀ Y Z, ∀ x ∈ Metric.ball (oneL E a) r, ‖chart (lieD Z (lieD Y f)) g x‖ ≤ K2 * ‖Y‖ * ‖Z‖)
    {x : Lie E a} (hx : x ∈ Metric.ball (oneL E a) r) :
    ‖fderiv ℝ (chart f g) x - fderiv ℝ (chart f g) (oneL E a)‖ ≤
      K * a * ‖invL x - oneL E a‖ + K2 * a * Q * ‖x - oneL E a‖ := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ x hx)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => ?_
  rw [ContinuousLinearMap.sub_apply, fderiv_chart hf g (hr hx)]
  have e1 : fderiv ℝ (chart f g) (oneL E a) Y = lieD Y f g := rfl
  have e2 : chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Y)) f) g x - chart (lieD Y f) g x =
      chart (lieD (toL (Matrix.of (invL x - oneL E a) * Matrix.of Y)) f) g x := by
    rw [chart_sub_lieD _ _ _ g (hr hx)]
    congr 2
    show (toL ((Matrix.of x)⁻¹ * Matrix.of Y) : Lie E a) - toL (Matrix.of Y) =
      toL (((Matrix.of x)⁻¹ - 1) * Matrix.of Y)
    rw [Matrix.sub_mul, Matrix.one_mul]
    rfl
  have hl := lipW (lieD_mem_Sm Y hf) (by positivity : 0 ≤ K2 * ‖Y‖) g hr hQ (fun Z z hz => hb2 Y Z z hz) hx
  rw [e1, show chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Y)) f) g x - lieD Y f g =
    (chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Y)) f) g x - chart (lieD Y f) g x) +
      (chart (lieD Y f) g x - lieD Y f g) by ring, e2]
  calc _ ≤ ‖chart (lieD (toL (Matrix.of (invL x - oneL E a) * Matrix.of Y)) f) g x‖ +
        ‖chart (lieD Y f) g x - lieD Y f g‖ := norm_add_le _ _
    _ ≤ K * (a * ‖invL x - oneL E a‖ * ‖Y‖) + K2 * ‖Y‖ * (a * Q) * ‖x - oneL E a‖ :=
        add_le_add ((hb1 _ x hx).trans (mul_le_mul_of_nonneg_left (norm_mulL _ _) hK)) hl
    _ = _ := by ring

theorem keyW {K K2 r0 c : ℝ} (hK : 0 ≤ K) (hK2 : 0 ≤ K2) (hr0 : 0 < r0) (hc : 0 < c) :
    ∃ δ > 0, ∀ (f : GA E a → ℂ) (g : GA E a) (w : ℝ), f ∈ Sm E a → 0 ≤ w →
      (∀ Z, ∀ x ∈ Metric.ball (oneL E a) r0, ‖chart (lieD Z f) g x‖ ≤ K * w * ‖Z‖) →
      (∀ Y Z, ∀ x ∈ Metric.ball (oneL E a) r0, ‖chart (lieD Z (lieD Y f)) g x‖ ≤ K2 * w * ‖Y‖ * ‖Z‖) →
      ∀ M ∈ Metric.ball (oneL E a) δ,
        ‖chart f g M - chart f g (oneL E a) - fderiv ℝ (chart f g) (oneL E a) (M - oneL E a)‖ ≤
          c * w * ‖M - oneL E a‖ := by
  set Q : ℝ := ‖oneL E a‖ + 1 with hQdef
  have ev1 : ∀ᶠ z in 𝓝 (oneL E a), z ∈ invSet E a := isOpen_invSet.mem_nhds isUnit_one
  have ev2 : ∀ᶠ z in 𝓝 (oneL E a), ‖invL z‖ < Q :=
    continuousAt_invL.norm.eventually (Iio_mem_nhds (by show ‖invL (oneL E a)‖ < Q; rw [invL_one]; linarith))
  have hct : ContinuousAt (fun z : Lie E a => K * a * ‖invL z - oneL E a‖ + K2 * a * Q * ‖z - oneL E a‖)
      (oneL E a) :=
    ((continuousAt_invL.sub continuousAt_const).norm.const_mul _).add
      ((continuousAt_id.sub continuousAt_const).norm.const_mul _)
  have ev3 : ∀ᶠ z in 𝓝 (oneL E a), K * a * ‖invL z - oneL E a‖ + K2 * a * Q * ‖z - oneL E a‖ ≤ c :=
    hct.eventually (Iic_mem_nhds (by simp [invL_one, hc]))
  have ev4 : ∀ᶠ z in 𝓝 (oneL E a), z ∈ Metric.ball (oneL E a) r0 := Metric.ball_mem_nhds _ hr0
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (ev1.and (ev2.and (ev3.and ev4)))
  have hr : Metric.ball (oneL E a) δ ⊆ invSet E a := fun z hz => (hball z hz).1
  have hQ : ∀ z ∈ Metric.ball (oneL E a) δ, ‖invL z‖ ≤ Q := fun z hz => (hball z hz).2.1.le
  refine ⟨δ, hδ, fun f g w hf hw hb1 hb2 M hM => ?_⟩
  exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => (contDiffAt_chart hf g (hr hz)).differentiableAt (by simp))
    (fun z hz => (ddW hf (mul_nonneg hK hw) (mul_nonneg hK2 hw) g hr hQ
      (fun Z x hx => hb1 Z x (hball x hx).2.2.2) (fun Y Z x hx => hb2 Y Z x (hball x hx).2.2.2) hz).trans (by
        have h3 := (hball z hz).2.2.1
        calc K * w * a * ‖invL z - oneL E a‖ + K2 * w * a * Q * ‖z - oneL E a‖ =
            w * (K * a * ‖invL z - oneL E a‖ + K2 * a * Q * ‖z - oneL E a‖) := by ring
          _ ≤ w * c := mul_le_mul_of_nonneg_left h3 hw
          _ = c * w := mul_comm _ _))
    (Metric.mem_ball_self hδ) hM

theorem wt_pos (hK1 : K1) (hk : 1 ≤ a) (M : ℕ) (g : GA E a) : 0 < wt M g :=
  pow_pos (lt_min one_pos ((hK1 E a hk).2.1 g)) M

theorem wt_cont (hK1 : K1) (hk : 1 ≤ a) (M : ℕ) : Continuous (wt M : GA E a → ℝ) :=
  (continuous_const.min (hK1 E a hk).1).pow M

def tf (hK1 : K1) (hk : 1 ≤ a) (M : ℕ) (θ : Sm E a) (hc : Continuous θ.1)
    (hb : ∃ C, ∀ g, ‖θ.1 g‖ ≤ C * wt M g) : XB E a :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => θ.1 g / (wt M g : ℂ))
    (hc.div (Complex.continuous_ofReal.comp (wt_cont hK1 hk M)) fun g => by
      exact_mod_cast (wt_pos hK1 hk M g).ne')
    hb.choose (fun g => by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (wt_pos hK1 hk M g).le,
        div_le_iff₀ (wt_pos hK1 hk M g)]
      exact hb.choose_spec g)

theorem nb (hK1 : K1) (hk : 1 ≤ a) (M : ℕ) {θ : GA E a → ℂ} {x : XB E a}
    (hx : ∀ g, x g = θ g / (wt M g : ℂ)) {B : ℝ} (hB : ‖x‖ ≤ B) (h : GA E a) : ‖θ h‖ ≤ B * wt M h := by
  have hw := wt_pos hK1 hk M h
  have e : θ h = x h * (wt M h : ℂ) := by
    rw [hx, div_mul_cancel₀ _ (by exact_mod_cast hw.ne')]
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
  exact mul_le_mul_of_nonneg_right ((x.norm_coe_le_norm h).trans hB) hw.le

theorem form_bd (hG : CuspDecayShortRowColumn) (hK1 : K1) (hk : 1 ≤ a) (M : ℕ) {π : CuspSub E a} (hπ : IsNormalised π)
    {θ : Sm E a} (hθ : θ ∈ π.V) : ∃ C, ∀ g, ‖θ.1 g‖ ≤ C * wt M g := by
  have h := (hG E a hk π hπ θ hθ 1).1
  have e : (fun g => θ.1 (g * 1)) = θ.1 := funext fun g => by rw [mul_one]
  rw [e] at h
  exact (hK1 E a hk).2.2.2.2.2 _ h M

theorem wtcmp (hH0 : H0) (hK1 : K1) (hk : 1 ≤ a) (M : ℕ) : ∃ r0 > 0, ∃ Bw : ℝ, 0 ≤ Bw ∧
    ∀ (F : GA E a → ℂ) (C : ℝ), 0 ≤ C → (∀ h, ‖F h‖ ≤ C * wt M h) →
      ∀ g, ∀ x ∈ Metric.ball (oneL E a) r0, ‖chart F g x‖ ≤ C * Bw * wt M g := by
  set Q : ℝ := ‖oneL E a‖ + 1 with hQdef
  have ev1 : ∀ᶠ z in 𝓝 (oneL E a), z ∈ invSet E a := isOpen_invSet.mem_nhds isUnit_one
  have ev2 : ∀ᶠ z in 𝓝 (oneL E a), ‖invL z‖ < Q :=
    continuousAt_invL.norm.eventually (Iio_mem_nhds (by show ‖invL (oneL E a)‖ < Q; rw [invL_one]; linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (ev1.and ev2)
  obtain ⟨B, N, hB, hP⟩ := (hH0 E a).2.2.2.2.2.1
  have hht := (hH0 E a).1
  have hpos := (hK1 E a hk).2.1
  have hle := (hK1 E a hk).2.2.1
  set P : ℝ := max (B * (1 + Q + (‖oneL E a‖ + r)) ^ N) 1 with hPdef
  have hP1 : 1 ≤ P := le_max_right _ _
  refine ⟨r, hr, P ^ M, by positivity, fun F C hC hF g x hx => ?_⟩
  obtain ⟨hxu, hxQ⟩ := hball x hx
  have hxu' : IsUnit (Matrix.of x) := hxu
  rw [chart, dif_pos hxu']
  set u := hxu'.unit with hu
  have e1 : (Matrix.of.symm (u⁻¹).val : LieI (InfinitePlace E) a) = invL x := by
    rw [Matrix.coe_units_inv, hu, IsUnit.unit_spec]; rfl
  have e2 : (Matrix.of.symm u.val : LieI (InfinitePlace E) a) = x := by
    rw [hu, IsUnit.unit_spec]; rfl
  have hx1 : ‖x‖ ≤ ‖oneL E a‖ + r := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  have hd : dmin (g * infGL E a u) ≤ P * dmin g := by
    have hP0 : 0 < P := by linarith
    have : dmin (g * infGL E a u) / P ≤ dmin g := by
      have : Nonempty {ξ : Fin a → E // ξ ≠ 0} :=
        ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hk⟩)⟩⟩
      refine le_ciInf fun ξ => ?_
      rw [div_le_iff₀ hP0]
      have h1 := hle (g * infGL E a u) ξ.1 ξ.2
      have h2 := hP u⁻¹ (g * infGL E a u) ξ.1 ξ.2
      rw [mul_assoc g, ← map_mul, mul_inv_cancel, map_one, mul_one, inv_inv, e1, e2] at h2
      have h3 := hht g ξ.1 ξ.2
      have h4 : (1 + ‖invL x‖ + ‖x‖) ^ N ≤ (1 + Q + (‖oneL E a‖ + r)) ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith) N
      calc dmin (g * infGL E a u) ≤ ht (g * infGL E a u) ξ.1 := h1
        _ ≤ B * (1 + ‖invL x‖ + ‖x‖) ^ N * ht g ξ.1 := h2
        _ ≤ B * (1 + Q + (‖oneL E a‖ + r)) ^ N * ht g ξ.1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hB) h3.le
        _ ≤ P * ht g ξ.1 := mul_le_mul_of_nonneg_right (le_max_left _ _) h3.le
        _ = ht g ξ.1 * P := mul_comm _ _
    rwa [div_le_iff₀ hP0, mul_comm] at this
  have hw : wt M (g * infGL E a u) ≤ P ^ M * wt M g := by
    unfold wt
    rw [← mul_pow]
    refine pow_le_pow_left₀ (le_min zero_le_one (hpos _).le) ?_ M
    rw [mul_min_of_nonneg _ _ (by linarith), mul_one]
    exact le_min ((min_le_left _ _).trans hP1) ((min_le_right _ _).trans hd)
  calc _ ≤ C * wt M (g * infGL E a u) := hF _
    _ ≤ C * (P ^ M * wt M g) := mul_le_mul_of_nonneg_left hw hC
    _ = _ := by ring

end WeightInverseContinuity

theorem koszulThree_of_det : jumpWindows.S1 → H0 → CuspDecayShortRowColumn → K1 → K3 := by
  intro hS1 hH0 hG hK1 E _ _ _ k hk M ρ J hW π hπ φ hφ
  have hc' : ∀ θ ∈ π.V, Continuous (θ : Sm E k).1 := fun θ hθ =>
    ContAut.continuous_of_isOpen_stab E k θ (π.cusp θ hθ).1.level
  have hb' : ∀ θ ∈ π.V, ∃ C, ∀ g, ‖(θ : Sm E k).1 g‖ ≤ C * wt M g := fun θ hθ =>
    WeightInverseContinuity.form_bd hG hK1 hk M hπ hθ
  have hm : ∀ Z θ, θ ∈ π.V → lie E k Z θ ∈ π.V := fun Z θ hθ => π.stable (.lie Z) θ hθ
  let T : ∀ θ : Sm E k, θ ∈ π.V → XB E k := fun θ hθ => WeightInverseContinuity.tf hK1 hk M θ (hc' θ hθ) (hb' θ hθ)
  have hT : ∀ θ hθ g, T θ hθ g = θ.1 g / (wt M g : ℂ) := fun _ _ _ => rfl
  have hJT : ∀ θ hθ, (J (T θ hθ) : GA E k → ℂ) = θ.1 := fun θ hθ => funext fun g => by
    rw [hW.mul, hT θ hθ, mul_div_cancel₀ _ (by exact_mod_cast (WeightInverseContinuity.wt_pos hK1 hk M g).ne')]
  have hJ : ∀ x g, x g = J x g / (wt M g : ℂ) := fun x g => by
    rw [hW.mul, mul_div_cancel_left₀ _ (by exact_mod_cast (WeightInverseContinuity.wt_pos hK1 hk M g).ne')]
  have hTadd : ∀ θ θ1 θ2 h h1 h2, θ = θ1 + θ2 → T θ h = T θ1 h1 + T θ2 h2 := by
    rintro θ θ1 θ2 h h1 h2 rfl
    ext g
    show T (θ1 + θ2) h g = T θ1 h1 g + T θ2 h2 g
    rw [hT _ h, hT _ h1, hT _ h2, Submodule.coe_add, Pi.add_apply, add_div]
  have hTsmul : ∀ (c : ℝ) θ θ1 h h1, θ = c • θ1 → T θ h = c • T θ1 h1 := by
    rintro c θ θ1 h h1 rfl
    ext g
    show T (c • θ1) h g = c • T θ1 h1 g
    rw [hT _ h, hT _ h1, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_div_assoc]
  let 𝒮 : Submodule ℂ (XB E k) :=
    { carrier := {x | ∃ θ ∈ π.V, (J x : GA E k → ℂ) = θ.1}
      add_mem' := by
        rintro x y ⟨θ, hθ, hx⟩ ⟨θ', hθ', hy⟩
        exact ⟨θ + θ', π.V.add_mem hθ hθ', by rw [map_add, BoundedContinuousFunction.coe_add, hx, hy, Submodule.coe_add]⟩
      zero_mem' := ⟨0, π.V.zero_mem, by rw [map_zero, BoundedContinuousFunction.coe_zero, Submodule.coe_zero]⟩
      smul_mem' := by
        rintro c x ⟨θ, hθ, hx⟩
        exact ⟨c • θ, π.V.smul_mem c hθ, by rw [map_smul, BoundedContinuousFunction.coe_smul, hx, Submodule.coe_smul]; rfl⟩ }
  obtain ⟨r0, hr0, Bw, hBw, hcb⟩ := WeightInverseContinuity.wtcmp (E := E) hH0 hK1 hk M
  have hder : ∀ v ∈ 𝒮, ∃ D : LieI (InfinitePlace E) k →L[ℝ] XB E k,
      HasFDerivAt (orb (ρ.comp (infGL E k)) v) D (oneI (InfinitePlace E) k) ∧ ∀ Z, D Z ∈ 𝒮 := by
    rintro v ⟨θ, hθ, hv⟩
    let Dl : LieI (InfinitePlace E) k →ₗ[ℝ] XB E k :=
      { toFun := fun Z => T (lie E k Z θ) (hm Z θ hθ)
        map_add' := fun Y Y' => hTadd _ _ _ (hm _ θ hθ) (hm _ θ hθ) (hm _ θ hθ)
          (by rw [map_add, LinearMap.add_apply])
        map_smul' := fun c Y => by
          rw [RingHom.id_apply]
          exact hTsmul c _ _ (hm _ θ hθ) (hm _ θ hθ) (by rw [map_smul, LinearMap.smul_apply]) }
    let D := LinearMap.toContinuousLinearMap Dl
    let Bl : LieI (InfinitePlace E) k →ₗ[ℝ] LieI (InfinitePlace E) k →ₗ[ℝ] XB E k :=
      LinearMap.mk₂ ℝ (fun Y Z => T (lie E k Z (lie E k Y θ)) (hm Z _ (hm Y θ hθ)))
        (fun Y Y' Z => hTadd _ _ _ (hm _ _ (hm _ θ hθ)) (hm _ _ (hm _ θ hθ)) (hm _ _ (hm _ θ hθ)) (by rw [map_add, LinearMap.add_apply, map_add]))
        (fun c Y Z => hTsmul c _ _ (hm _ _ (hm _ θ hθ)) (hm _ _ (hm _ θ hθ)) (by rw [map_smul, LinearMap.smul_apply, LinearMap.map_smul_of_tower]))
        (fun Y Z Z' => hTadd _ _ _ (hm _ _ (hm _ θ hθ)) (hm _ _ (hm _ θ hθ)) (hm _ _ (hm _ θ hθ)) (by rw [map_add, LinearMap.add_apply]))
        (fun c Y Z => hTsmul c _ _ (hm _ _ (hm _ θ hθ)) (hm _ _ (hm _ θ hθ)) (by rw [map_smul, LinearMap.smul_apply]))
    obtain ⟨K2, hK2, hB2⟩ := WeightInverseContinuity.bil_bound Bl
    have hb1 : ∀ Z h, ‖lieD Z θ.1 h‖ ≤ ‖D‖ * ‖Z‖ * wt M h := fun Z h =>
      WeightInverseContinuity.nb hK1 hk M (x := D Z) (fun g => rfl) (D.le_opNorm Z) h
    have hb2 : ∀ Y Z h, ‖lieD Z (lieD Y θ.1) h‖ ≤ K2 * ‖Y‖ * ‖Z‖ * wt M h := fun Y Z h =>
      WeightInverseContinuity.nb hK1 hk M (x := Bl Y Z) (fun g => rfl) (hB2 Y Z) h
    have horb : ∀ N g, orb (ρ.comp (infGL E k)) v N g = chart θ.1 g N / (wt M g : ℂ) := by
      intro N g
      rw [hJ]
      unfold orb chart
      split_ifs with h
      · rw [MonoidHom.comp_apply, hW.inter, Rt_apply, hv]
      · simp
    refine ⟨D, ?_, fun Z => ⟨lie E k Z θ, hm Z θ hθ, hJT _ (hm Z θ hθ)⟩⟩
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
    obtain ⟨δ, hδ, hkey⟩ := WeightInverseContinuity.keyW (a := k) (E := E) (K := ‖D‖ * Bw) (K2 := K2 * Bw)
      (by positivity) (by positivity) hr0 hc
    filter_upwards [Metric.ball_mem_nhds (0 : LieI (InfinitePlace E) k) hδ] with h hh
    obtain ⟨N, rfl⟩ : ∃ N : LieI (InfinitePlace E) k, h = N - oneL E k := ⟨oneL E k + h, by abel⟩
    have hN : N ∈ Metric.ball (oneL E k) δ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact mem_ball_zero_iff.1 hh
    rw [show oneI (InfinitePlace E) k + (N - oneL E k) = N from add_sub_cancel _ _]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun g => ?_
    have hw := WeightInverseContinuity.wt_pos hK1 hk M g
    have e : (orb (ρ.comp (infGL E k)) v N - orb (ρ.comp (infGL E k)) v (oneI (InfinitePlace E) k) -
        D (N - oneL E k)) g = (chart θ.1 g N - chart θ.1 g (oneL E k) -
          fderiv ℝ (chart θ.1 g) (oneL E k) (N - oneL E k)) / (wt M g : ℂ) := by
      rw [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_sub, Pi.sub_apply, Pi.sub_apply,
        horb, horb, sub_div, sub_div]
      rfl
    rw [e, norm_div, Complex.norm_real, Real.norm_of_nonneg hw.le, div_le_iff₀ hw]
    have := hkey θ.1 g (wt M g) θ.2 hw.le
      (fun Z x hx => (hcb (lieD Z θ.1) (‖D‖ * ‖Z‖) (by positivity) (hb1 Z) g x hx).trans (le_of_eq (by ring)))
      (fun Y Z x hx => (hcb (lieD Z (lieD Y θ.1)) (K2 * ‖Y‖ * ‖Z‖) (by positivity) (hb2 Y Z) g x hx).trans
        (le_of_eq (by ring))) N hN
    calc _ ≤ c * wt M g * ‖N - oneL E k‖ := this
      _ = c * ‖N - oneL E k‖ * wt M g := by ring
  have key := hS1 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly 𝒮 hder
  exact ⟨T φ hφ, hJT φ hφ, key _ ⟨φ, hφ, hJT φ hφ⟩⟩

end PositivityTheory.AdelicQuotientData

end
