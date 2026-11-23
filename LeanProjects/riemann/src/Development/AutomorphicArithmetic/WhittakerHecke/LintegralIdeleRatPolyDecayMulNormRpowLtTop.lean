import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import GroundTheory.GlobalFields.TateThesis.GlobalZeta
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem mult_eq_one (w : InfinitePlace ℚ) : w.mult = 1 := by
  simp [InfinitePlace.mult, IsTotallyReal.isReal w]

private theorem lint_real (w : InfinitePlace ℚ) {s : ℝ} (hs : 1 < s) :
    ∫⁻ z, ENNReal.ofReal ((1 + ‖z‖) ^ (-s)) ∂infinitePlaceMeasure w < ∞ := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hm : Measurable fun z : w.Completion ↦ ENNReal.ofReal ((1 + ‖z‖) ^ (-s)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_const.add continuous_norm).rpow_const fun z ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg z)).ne').measurable
  rw [infinitePlaceMeasure_of_isReal hw,
    lintegral_map hm (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.measurable]
  have h : ∀ y : ℝ, ‖(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm y‖ = ‖y‖ := fun y ↦ by
    rw [← norm_isometryEquivRealOfIsReal hw, IsometryEquiv.apply_symm_apply]
  simp_rw [h]
  exact finite_integral_one_add_norm (by simpa using hs)

private theorem int_place (w : InfinitePlace ℚ) {x : ℝ} (h1 : 1 < x) {r : ℕ} (hr : x < r) :
    Integrable (fun z : (w.Completion)ˣ ↦ ‖(z : w.Completion)‖ ^ x / (1 + ‖(z : w.Completion)‖) ^ r)
      (infinitePlaceUnitsMeasure w) := by
  have hG : Continuous fun z : w.Completion ↦ ‖z‖ ^ x / (1 + ‖z‖) ^ r :=
    (continuous_norm.rpow_const fun _ ↦ Or.inr (by linarith)).div
      ((continuous_const.add continuous_norm).pow r) fun _ ↦ by positivity
  refine ⟨(hG.comp Units.continuous_val).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z ↦ by positivity)]
  refine (lintegral_unitsMeasure_le (infinitePlaceMeasure w) w.mult
    (g := fun z ↦ ENNReal.ofReal (‖z‖ ^ x / (1 + ‖z‖) ^ r))
    (ENNReal.measurable_ofReal.comp hG.measurable)).trans_lt ?_
  refine lt_of_le_of_lt (lintegral_mono fun z ↦ ?_) (lint_real w (s := r - x + 1) (by linarith))
  rw [← ENNReal.ofReal_mul (by positivity), mult_eq_one, pow_one]
  refine ENNReal.ofReal_le_ofReal ?_
  set t := ‖z‖
  have ht : 0 ≤ t := norm_nonneg _
  have ha : 1 ≤ 1 + t := by linarith
  have hapos : 0 < 1 + t := by linarith
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith), zero_div, mul_zero]
    positivity
  · have e1 : t⁻¹ * (t ^ x / (1 + t) ^ r) = t ^ (x - 1) * ((1 + t) ^ (r : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast (1 + t) r, Real.rpow_sub hpos, Real.rpow_one, div_eq_mul_inv,
        div_eq_mul_inv]
      ring
    have e2 : (1 + t) ^ (-((r : ℝ) - x + 1)) = (1 + t) ^ (x - 1) * ((1 + t) ^ (r : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hapos.le, ← Real.rpow_add hapos]
      congr 1
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow ht (by linarith) (by linarith)) (by positivity)

private noncomputable def hInf (x : ℝ) (r : ℕ) (a : (InfiniteAdeleRing ℚ)ˣ) : ℝ :=
  ∏ w : InfinitePlace ℚ, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ x / (1 + ‖(a : InfiniteAdeleRing ℚ) w‖) ^ r

private theorem int_hInf {x : ℝ} (h1 : 1 < x) {r : ℕ} (hr : x < r) :
    Integrable (hInf x r) (infiniteIdeleMeasure ℚ) := by
  have h := Integrable.fintype_prod_dep (𝕜 := ℝ)
    (f := fun (w : InfinitePlace ℚ) (z : (w.Completion)ˣ) ↦
      ‖(z : w.Completion)‖ ^ x / (1 + ‖(z : w.Completion)‖) ^ r)
    (μ := fun w ↦ infinitePlaceUnitsMeasure w) fun w ↦ int_place w h1 hr
  rw [infiniteIdeleMeasure]
  refine (integrable_map_equiv (infiniteUnitsEquiv ℚ).symm.toHomeomorph.toMeasurableEquiv _).2 ?_
  exact h

private theorem abs_re (y : IdeleGroup ℚ) :
    |re (y : A ℚ)| = ‖((IdeleGroup.toInfinite ℚ y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ := by
  have hw : (Rat.infinitePlace).IsReal := IsTotallyReal.isReal _
  have e : re (y : A ℚ) = InfinitePlace.Completion.isometryEquivRealOfIsReal hw
      (((IdeleGroup.toInfinite ℚ y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) Rat.infinitePlace) := rfl
  rw [e, ← Real.norm_eq_abs, norm_isometryEquivRealOfIsReal]

theorem UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top :
    ∀ (K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact K → ∀ x : ℝ, 1 < x → ∀ r : ℕ, x < r →
        ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K then ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ r)⁻¹ * ab y ^ x) else 0) ∂(ideleMeasure ℚ) < ⊤ := by
  intro K hK x hx r hr
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hK
  have hG : Integrable (fun y : IdeleGroup ℚ ↦
      hInf x r (IdeleGroup.toInfinite ℚ y) * finiteZetaBound L x (IdeleGroup.toFinite ℚ y))
      (ideleMeasure ℚ) := by
    have h := (int_hInf hx hr).mul_prod (integrable_finiteZetaBound L hx)
    exact ((measurePreserving_prodEquiv ℚ).integrable_comp_emb
      (IdeleGroup.prodEquiv ℚ).toHomeomorph.measurableEmbedding).2 h
  refine lt_of_le_of_lt (lintegral_mono fun y ↦ ?_) hG.lintegral_lt_top
  split_ifs with hy
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hb : ((IdeleGroup.toFinite ℚ y : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ idealFiniteAdeles L :=
      hL hy
    rw [finiteZetaBound, if_pos hb, hInf, ab, ideleModule_rpow_eq, abs_re,
      Fintype.prod_subsingleton _ Rat.infinitePlace, Fintype.prod_subsingleton _ Rat.infinitePlace,
      mult_eq_one]
    simp only [Nat.cast_one, one_mul]
    rw [div_eq_mul_inv]
    ring_nf
  · exact zero_le
