import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.KSuppPf

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem inv_contAt (A : Mat n) (hA : A.det ≠ 0) : ContinuousAt (fun B : Mat n => B⁻¹) A := by
  apply continuousAt_matrix_inv
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hA

theorem lg_contAt (A : Mat n) (hA : A.det ≠ 0) : ContinuousAt lg A := by
  have hi := inv_contAt A hA
  unfold lg
  refine ContinuousAt.log ?_ ?_
  · refine continuousAt_const.add ?_
    refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
    refine ContinuousAt.add (f := fun y : Mat n => ‖y a b‖ ^ 2) (g := fun y : Mat n => ‖y⁻¹ a b‖ ^ 2) ?_ ?_
    · exact ((continuous_norm.comp ((continuous_apply b).comp (continuous_apply a))).continuousAt).pow 2
    · exact (continuous_norm.continuousAt.comp
        (((continuous_apply b).comp (continuous_apply a)).continuousAt.comp hi)).pow 2
  · have : 0 ≤ ∑ a, ∑ b, (‖A a b‖ ^ 2 + ‖A⁻¹ a b‖ ^ 2) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
    positivity

theorem det_ne_of_posDef (x : Mat n) (h : (x * xᴴ).PosDef) : x.det ≠ 0 := by
  intro h0
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  rw [Matrix.det_mul, h0, zero_mul] at hu
  exact not_isUnit_zero hu

theorem det_inv_ne (A : Mat n) (h : A.det ≠ 0) : (A⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero h

theorem det_ct_ne (A : Mat n) (h : A.det ≠ 0) : (Aᴴ).det ≠ 0 := by
  rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 h

theorem hOf_comb (hb : HbFacts) (s : ℝ) (v : Fin n × Fin n → ℝ) :
    hOf (s • v + (1 - s) • oPt n) = (s : ℂ) • hOf v + (((1 - s : ℝ)) : ℂ) • (1 : Mat n) := by
  have h1 : hOf (oPt n) = 1 := (hb n).2.2.1 1 Matrix.isHermitian_one
  rw [← h1]
  unfold hOf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

def Kset (n : ℕ) (B : ℝ) : Set (Mat n × Mat n) :=
  {p | p.1 * p.2 = 1} ∩ {p | ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ B}

theorem isCompact_Kset (B : ℝ) : IsCompact (Kset n B) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.matrix_mul continuous_snd) continuous_const
    · refine isClosed_le (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_) continuous_const
      exact ((continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp continuous_fst))).pow 2).add
        ((continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp continuous_snd))).pow 2)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|B| + 1, fun p hp => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hent : ∀ a b, ‖p.1 a b‖ ≤ |B| + 1 ∧ ‖p.2 a b‖ ≤ |B| + 1 := by
      intro a b
      have hle : ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ B := by
        refine le_trans ?_ hp.2
        refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2))
          (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a))
        exact Finset.single_le_sum (f := fun b => ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)
          (fun b _ => by positivity) (Finset.mem_univ b)
      have h1 : ‖p.1 a b‖ ^ 2 ≤ |B| := le_trans (by nlinarith [sq_nonneg ‖p.2 a b‖]) (le_abs_self B)
      have h2 : ‖p.2 a b‖ ^ 2 ≤ |B| := le_trans (by nlinarith [sq_nonneg ‖p.1 a b‖]) (le_abs_self B)
      constructor
      · nlinarith [norm_nonneg (p.1 a b), abs_nonneg B, sq_nonneg (‖p.1 a b‖ - 1)]
      · nlinarith [norm_nonneg (p.2 a b), abs_nonneg B, sq_nonneg (‖p.2 a b‖ - 1)]
    have hB : 0 ≤ |B| + 1 := by positivity
    rw [Prod.norm_def, max_le_iff]
    exact ⟨(Matrix.norm_le_iff hB).2 fun a b => (hent a b).1, (Matrix.norm_le_iff hB).2 fun a b => (hent a b).2⟩

theorem continuous_coords : Continuous (coords : Mat n → Fin n × Fin n → ℝ) := by
  apply continuous_pi
  intro p
  unfold coords
  exact Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)

theorem ksupp_of (hb : HbFacts) (hc : ConeSt) : KSupp := by
  intro hS n V _ _ σ hσ hσ2 Fr k Γ T R hk z hz hinj c
  obtain ⟨hopen, hconv, -⟩ := hc n
  obtain ⟨R', hR'⟩ := hS n z hz hinj R
  set C : Set (Fin n × Fin n → ℝ) := (fun p : Mat n × Mat n => coords (p.1 * p.1ᴴ)) '' Kset n (Real.exp R') with hCdef
  have hdet : ∀ v ∈ cone n, (σ v).det ≠ 0 := fun v hv =>
    det_ne_of_posDef _ (by rw [hσ2 v hv]; exact hv)
  have hdz : (diagonal z).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => fun h0 => by have := hz a; rw [h0, norm_zero] at this; exact zero_ne_one this
  refine ⟨C, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hd1 : p.1.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hp.1
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hu : IsUnit p.1 := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd1)
    show (hOf (coords (p.1 * p.1ᴴ))).PosDef
    rw [(hb n).2.2.1 _ (Matrix.isHermitian_mul_conjTranspose_self _)]
    have := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := (1 : Mat n)) hu).2 Matrix.PosDef.one
    simpa [Matrix.star_eq_conjTranspose] using this
  · exact (isCompact_Kset _).image (continuous_coords.comp (continuous_fst.matrix_mul continuous_fst.matrix_conjTranspose))
  · intro s hs v hv hvC
    have ho : oPt n ∈ cone n := (hb n).2.2.2.2.2.2.2
    have hP1 : s • v + (1 - s) • oPt n ∈ cone n := hconv hv ho hs.1 (by linarith [hs.2]) (by ring)

    have hgt : R < lg ((σ (s • v + (1 - s) • oPt n))⁻¹ * diagonal z * (σ v)ᴴ⁻¹) := by
      by_contra hle
      push Not at hle
      have hyR := hR' s hs (σ (s • v + (1 - s) • oPt n)) (hdet _ hP1) (σ v) (hdet v hv)
        (by rw [hσ2 _ hP1, hσ2 v hv, hOf_comb hb]) hle
      apply hvC
      refine ⟨(σ v, (σ v)⁻¹), ⟨Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet v hv)), ?_⟩, ?_⟩
      · have h1 : 0 ≤ ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2) :=
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
        have h2 : Real.log (1 + ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2)) ≤ R' := hyR
        have h3 := (Real.log_le_iff_le_exp (by positivity)).1 h2
        show ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2) ≤ Real.exp R'
        linarith
      · show coords (σ v * (σ v)ᴴ) = v
        rw [hσ2 v hv]; exact (hb n).2.2.2.1 v

    have hσc : ∀ w ∈ cone n, ContinuousAt σ w := fun w hw =>
      (hσ.continuousOn).continuousAt (hopen.mem_nhds hw)
    have hA : ((σ (s • v + (1 - s) • oPt n))⁻¹ * diagonal z * (σ v)ᴴ⁻¹).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero (det_inv_ne _ (hdet _ hP1)) hdz) (det_inv_ne _ (det_ct_ne _ (hdet v hv)))
    have hf1 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.1)⁻¹)
        (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := fun B : Mat n => B⁻¹) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ w.1)
        (inv_contAt _ (hdet _ hP1))
        (ContinuousAt.comp (g := σ) (f := Prod.fst) (x := (s • v + (1 - s) • oPt n, v)) (hσc _ hP1) continuousAt_fst)
    have hf2 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.2)ᴴ⁻¹)
        (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := fun B : Mat n => B⁻¹) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.2)ᴴ)
        (inv_contAt _ (det_ct_ne _ (hdet v hv)))
        (ContinuousAt.comp (g := fun B : Mat n => Bᴴ) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ w.2)
          (continuous_id.matrix_conjTranspose).continuousAt
          (ContinuousAt.comp (g := σ) (f := Prod.snd) (x := (s • v + (1 - s) • oPt n, v)) (hσc v hv) continuousAt_snd))
    have hΦ : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
        lg ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹)) (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := lg) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
          (σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹) (lg_contAt _ hA) (by
        have h3 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.1)⁻¹ * diagonal z)
            (s • v + (1 - s) • oPt n, v) := hf1.mul continuousAt_const
        exact h3.mul hf2)
    have e1 := hΦ.eventually (Ioi_mem_nhds hgt)
    have e2 : ∀ᶠ w in nhds (s • v + (1 - s) • oPt n, v), w ∈ cone n ×ˢ cone n :=
      (hopen.prod hopen).mem_nhds ⟨hP1, hv⟩
    filter_upwards [e1, e2] with w hw1 hw2
    have hGL : ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹) ∈ GLs n := by
      show ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero (det_inv_ne _ (hdet _ hw2.1)) hdz) (det_inv_ne _ (det_ct_ne _ (hdet _ hw2.2)))
    have hk0 := hk _ hGL hw1
    simp only [Kc, Kf, hk0, mul_zero, zero_mul, smul_zero]

end PositivityTheory.RgBcC.LfSt.KSuppPf
