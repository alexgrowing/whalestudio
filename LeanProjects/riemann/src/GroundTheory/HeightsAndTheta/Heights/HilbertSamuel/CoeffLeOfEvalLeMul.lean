import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelTrivLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftIntersectionPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftDegreePolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftNefBig
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftVolumeBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

namespace ArithmeticVolumeDegreeZero

theorem arithmeticVolume_nonneg {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) :
    0 ≤ arVolP P La a D := by
  unfold arVolP
  have hu : ∀ k : ℕ, 0 ≤ smallSectionCount P La (a * k) / (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
    fun k => div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  by_cases hb : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => smallSectionCount P La (a * k) / (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)))
  · exact le_limsup_of_frequently_le (Frequently.of_forall hu) hb
  · rw [Real.limsup_of_not_isBoundedUnder hb]

theorem charZero_of_horizontal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (MvPolynomial.C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (MvPolynomial.C (n : ℤ)) = 0
    rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  have h' : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := hmem
  rw [h] at h'
  exact_mod_cast (Submodule.mem_bot _).mp h'

theorem coeff_le_of_eval_le_mul {D : ℕ} (p r : Polynomial ℝ) {C : ℝ} (hC : 0 ≤ C) (hp : p.natDegree ≤ D + 1)
    (hr : r.natDegree ≤ D) (hrD : r.coeff D ≤ 0)
    (h : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ)) : p.coeff (D + 1) ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  set g : Polynomial ℝ := p - Polynomial.C C * ((Polynomial.X + 1) * r) with hg
  have hr1 : r.coeff (D + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hgc : g.coeff (D + 1) = p.coeff (D + 1) - C * r.coeff D := by
    rw [hg, Polynomial.coeff_sub, Polynomial.coeff_C_mul, add_mul, one_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_mul, hr1, add_zero]
  have hgpos : 0 < g.coeff (D + 1) := by
    rw [hgc]; nlinarith
  have hgdeg : g.natDegree ≤ D + 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le hp ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_mul_le).trans ?_
    have : (Polynomial.X + 1 : Polynomial ℝ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le ?_)
      simp
    omega
  have hgnat : g.natDegree = D + 1 :=
    le_antisymm hgdeg (Polynomial.le_natDegree_of_ne_zero hgpos.ne')
  have hlead : 0 ≤ g.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hgnat]; exact hgpos.le
  have hdeg : 0 < g.degree := by
    rw [Polynomial.degree_eq_natDegree (fun h0 => by simp [h0] at hgpos), hgnat]
    exact_mod_cast Nat.succ_pos D
  have ht := (g.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead).comp tendsto_natCast_atTop_atTop
  obtain ⟨q, hq1, hq⟩ := ((eventually_ge_atTop 1).and (ht.eventually (eventually_gt_atTop 0))).exists
  have hev : g.eval (q : ℝ) = p.eval (q : ℝ) - C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    simp only [hg, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    ring
  have := h q hq1
  simp only [Function.comp_apply] at hq
  linarith

end ArithmeticVolumeDegreeZero

theorem ArithmeticVolumeDegreeZero.proof (hB : G6.StatementB) (hN : ShiftNefBig.Statement) (hV : ShiftVolumeBound.Statement)
    (hI : ShiftIntersectionPolynomial.Statement) (hG : ShiftDegreePolynomial.Statement) :
    ArithmeticVolumeDegreeZero.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc hdeg
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  refine le_trans ?_ (ArithmeticVolumeDegreeZero.arithmeticVolume_nonneg _ _ _ _)
  obtain ⟨C, hC0, hC⟩ := hV K ι Ω y D A P0 hD har hb hP0 hs hnef hc
  obtain ⟨p, hpdeg, hpc, hp⟩ := hI K ι II (mCoordIdeal y) (D + 1) A (fsH ι) hII har hs.1
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)
  obtain ⟨r, hrdeg, hrc, hr⟩ := hG K ι (mCoordIdeal y) D A.a ((1 : ℤ) • (fsH ι).a) har
  have hbound : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    intro q hq
    rw [← hp q, ← hr q]
    exact (hB K ι Ω y D _ P0 II hD hII har hb (hN K ι Ω y D A P0 hD har hb hP0 hs hnef hc q hq)).trans (hC q hq)
  rw [← hpc]
  exact ArithmeticVolumeDegreeZero.coeff_le_of_eval_le_mul p r hC0 hpdeg hrdeg (by rw [hrc]; exact_mod_cast hdeg) hbound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
