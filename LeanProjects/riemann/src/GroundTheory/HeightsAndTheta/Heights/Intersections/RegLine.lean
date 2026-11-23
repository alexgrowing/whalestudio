import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ‖eval z (map (Int.castRingHom ℂ) t)‖ / E.h z

theorem logNorm_eq_log_secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm E t z = Real.log (secNorm E t z) := rfl

theorem secNorm_nonneg (E : HermLine ι) (t : MRing ι) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 ≤ secNorm E t z :=
  div_nonneg (norm_nonneg _) (E.pos z hz).le

theorem secNorm_smul {E : HermLine ι} {t : MRing ι} {a : K → ℕ} (hE : ∀ k, E.a k = a k)
    (ht : IsMultiHomog t a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    secNorm E t (fun p => c p.1 * z p) = secNorm E t z := by
  have he := eval_bsmul_of_isMultiHomog ht c z
  have hh : E.h (bsmul c z) = (∏ k, ‖c k‖ ^ E.a k) * E.h z := E.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ E.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ E.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hE k, zpow_natCast]
  change ‖eval (bsmul c z) (map (Int.castRingHom ℂ) t)‖ / E.h (bsmul c z) = _
  rw [he, hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']
  rfl

def regLine (E : HermLine ι) (t : MRing ι) (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a)
    (ε : ℝ) : HermLine ι :=
  HermLine.ofWeight (fun z => -(Real.log (secNorm E t z ^ 2 + ε) / 2)) (by
    intro c z hc
    obtain ⟨a, hE, hta⟩ := ht
    simp only [secNorm_smul hE hta hc z])

variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}

theorem regLine_a : (regLine E t ht ε).a = 0 := rfl

theorem regLine_h (z : (Σ k, ι k) → ℂ) :
    (regLine E t ht ε).h z = Real.exp (Real.log (secNorm E t z ^ 2 + ε) / 2) := by
  simp [regLine, HermLine.ofWeight]

theorem log_regLine_h (z : (Σ k, ι k) → ℂ) :
    Real.log ((regLine E t ht ε).h z) = Real.log (secNorm E t z ^ 2 + ε) / 2 := by
  rw [regLine_h, Real.log_exp]

theorem contDiff_eval_map (t : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) t)) := by
  induction t using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (contDiff_apply ℝ ℂ v)

theorem isSmoothHerm_regLine (hE : IsSmoothHerm E) (hε : 0 < ε) : IsSmoothHerm (regLine E t ht ε) := by
  unfold IsSmoothHerm
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_eval_map t)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2 / E.h z ^ 2 + ε)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hn.contDiffOn.div (hE.pow 2) fun z hz => pow_ne_zero _ (E.pos z hz).ne').add contDiffOn_const
  have hl := (hq.log fun z hz => (add_pos_of_nonneg_of_pos
    (div_nonneg (sq_nonneg _) (sq_nonneg _)) hε).ne').div_const 2
  refine (Real.contDiff_exp.comp_contDiffOn hl).congr fun z _ => ?_
  rw [regLine_h, secNorm, div_pow]
  rfl

theorem logNorm_le_log_regLine_h (hε : 0 ≤ ε) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ht0 : eval z (map (Int.castRingHom ℂ) t) ≠ 0) :
    logNorm E t z ≤ Real.log ((regLine E t ht ε).h z) := by
  rw [log_regLine_h, logNorm_eq_log_secNorm]
  have hpos : 0 < secNorm E t z := div_pos (norm_pos_iff.mpr ht0) (E.pos z hz)
  have h2 : Real.log (secNorm E t z) = Real.log (secNorm E t z ^ 2) / 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [h2]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by linarith)) (by norm_num)

end Objects

theorem isMultiHomog_planeCoordinate (i : Fin 3) : ∃ a : Unit → ℕ, (∀ k, (fsLine 3).a k = a k) ∧ IsMultiHomog (Xc 3 i) a := by
  obtain ⟨a, ha, hm, -⟩ := isSectionOn_coordinate_plane i
  exact ⟨a, ha, hm⟩

theorem regLine.inhabited :
    IsSmoothHerm (regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1) ∧
      (regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1).a = 0 ∧
      ∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 3))), eval z (map (Int.castRingHom ℂ) (Xc 3 0)) ≠ 0 →
        logNorm (fsLine 3) (Xc 3 0) z ≤
          Real.log ((regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1).h z) :=
  ⟨isSmoothHerm_regLine (isSmoothHerm_fsLine 3) one_pos, rfl,
    fun _ hz h0 => logNorm_le_log_regLine_h zero_le_one hz.1 h0⟩

end GroundTheory.Heights₂.Heights.Inter
