import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Unimod

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim HU

variable {k r : ℕ}

def BallConj : Prop :=
  ∀ (k r : ℕ) (ρ : ℝ) (q : Mat k r), q ∈ UWb k r → qᴴ * q = 1 →
    rmulM q ⁻¹' bBall k r ρ ⊆ lmulM q ⁻¹' bBall k r ρ

def rmulE (p : Mat k r) (hp : IsUnit p.det) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulM p
  invFun := rmulM p⁻¹
  left_inv x := by
    show (Matrix.of x * p) * p⁻¹ = x
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hp, Matrix.mul_one]; rfl
  right_inv x := by
    show (Matrix.of x * p⁻¹) * p = x
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.mul_one]; rfl
  measurable_toFun := rmulM_meas p
  measurable_invFun := rmulM_meas p⁻¹

theorem lr_comm (s p : Mat k r) : lmulM s ∘ rmulM p = rmulM p ∘ lmulM s := by
  funext x
  show s * (Matrix.of x * p) = (s * Matrix.of x) * p
  rw [Matrix.mul_assoc]

theorem rmul_haar (ν : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) ν) (p : Mat k r) (hp : p ∈ UWb k r) :
    IsHaarOn (UWb k r) (ν.map (rmulM p)) := by
  obtain ⟨hσ, h0, hc, hl⟩ := hH
  have hu := uwb_unit hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rmulE p hu).sigmaFinite_map
  · rw [Ne, Measure.map_eq_zero_iff (rmulM_meas p).aemeasurable]; exact h0
  · have hms : MeasurableSet {x : Mt k r | Matrix.of x ∉ UWb k r} := amb_closed.isOpen_compl.measurableSet
    rw [Measure.map_apply (rmulM_meas p) hms]
    refine measure_mono_null (fun x hx => ?_) hc
    intro hxm
    apply hx
    show Matrix.of x * p ∈ UWb k r
    exact uwb_mul hxm hp
  · intro s hs
    rw [Measure.map_map (lmulM_cont s).measurable (rmulM_meas p), lr_comm,
      ← Measure.map_map (rmulM_meas p) (lmulM_cont s).measurable, hl s hs]

theorem gauge_ball (ν : Measure (Mt k r)) (hG : IsGaugeOn k r (UWb k r) ν) :
    ∃ ρ : ℝ, 0 < ν (bBall k r ρ) ∧ ν (bBall k r ρ) < ⊤ := by
  have h := hG.2.eventually_const_lt (show (0 : ℝ) < 1 from one_pos)
  obtain ⟨ρ, hρ⟩ := h.exists
  refine ⟨ρ, ?_, ?_⟩
  · rcases eq_or_ne (ν (bBall k r ρ)) 0 with h0 | h0
    · exfalso
      have : (ν (expBall (k := k) (r := r) (UWb k r) ρ)).toReal = 0 := by
        show (ν (bBall k r ρ)).toReal = 0
        rw [h0]; rfl
      rw [this, zero_div] at hρ; exact lt_irrefl _ hρ
    · exact pos_iff_ne_zero.2 h0
  · rcases eq_or_ne (ν (bBall k r ρ)) ⊤ with h0 | h0
    · exfalso
      have : (ν (expBall (k := k) (r := r) (UWb k r) ρ)).toReal = 0 := by
        show (ν (bBall k r ρ)).toReal = 0
        rw [h0]; rfl
      rw [this, zero_div] at hρ; exact lt_irrefl _ hρ
    · exact lt_top_iff_ne_top.2 h0

theorem rmul_scale (ν : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) ν) (p : Mat k r) (hp : p ∈ UWb k r)
    (s : Set (Mt k r)) (h0 : ν s ≠ 0) (ht : ν s ≠ ⊤) :
    ν.map (rmulM p) = (ν.map (rmulM p) s / ν s) • ν := by
  have h1 := rmul_haar ν hH p hp
  obtain ⟨hσ1, h01, hc1, hl1⟩ := h1
  obtain ⟨hσ2, h02, hc2, hl2⟩ := hH
  have i1 : SigmaFinite (pull (ν.map (rmulM p))) := pull_sigmaFinite _
  have i2 : SigmaFinite (pull ν) := pull_sigmaFinite ν
  have i3 : (pull (ν.map (rmulM p))).IsMulLeftInvariant := pull_left _ hl1
  have i4 : (pull ν).IsMulLeftInvariant := pull_left ν hl2
  have key := measure_eq_div_smul (pull (ν.map (rmulM p))) (pull ν) (s := inc ⁻¹' s)
    (by rw [pull_apply ν hc2]; exact h0) (by rw [pull_apply ν hc2]; exact ht)
  calc ν.map (rmulM p) = (pull (ν.map (rmulM p))).map inc := (map_pull _ hc1).symm
    _ = ((pull (ν.map (rmulM p)) (inc ⁻¹' s) / pull ν (inc ⁻¹' s)) • pull ν).map inc := by rw [← key]
    _ = _ := by rw [Measure.map_smul, map_pull ν hc2, pull_apply _ hc1, pull_apply ν hc2]

theorem one_of_le (c c' : ℝ≥0∞) (h : c * c' = 1) (hc : c ≤ 1) (hc' : c' ≤ 1) : c = 1 := by
  refine le_antisymm hc ?_
  calc 1 = c * c' := h.symm
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c

theorem one_of_sq (c : ℝ≥0∞) (h : c * c = 1) : c = 1 := by
  rcases le_total c 1 with hc | hc
  · exact one_of_le c c h hc hc
  · refine le_antisymm ?_ hc
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * c := by gcongr
      _ = 1 := h

theorem map_rmul_one (ν : Measure (Mt k r)) : ν.map (rmulM (1 : Mat k r)) = ν := by
  have : (rmulM (1 : Mat k r) : Mt k r → Mt k r) = id := by
    funext x; unfold rmulM; rw [Matrix.mul_one]; rfl
  rw [this, Measure.map_id]

theorem scale_mul_one (ν : Measure (Mt k r)) (p p' : Mat k r) (hpp : p * p' = 1) (s : Set (Mt k r))
    (h0 : ν s ≠ 0) (ht : ν s ≠ ⊤) (c c' : ℝ≥0∞) (hc : ν.map (rmulM p) = c • ν)
    (hc' : ν.map (rmulM p') = c' • ν) : c * c' = 1 := by
  have e : ν = (c * c') • ν := by
    calc ν = ν.map (rmulM (p * p')) := by rw [hpp, map_rmul_one]
      _ = (ν.map (rmulM p)).map (rmulM p') := by
          rw [Measure.map_map (rmulM_meas p') (rmulM_meas p), rmulM_comp]
      _ = (c * c') • ν := by rw [hc, Measure.map_smul, hc', smul_smul]
  have e2 := congrArg (fun m : Measure (Mt k r) => m s) e
  simp only [Measure.smul_apply, smul_eq_mul] at e2
  exact (ENNReal.mul_left_inj h0 ht).1 (show (c * c') * ν s = 1 * ν s by rw [one_mul]; exact e2.symm)

theorem unitInv_of (hB : BallConj) : UnitInv := by
  intro k r ν hk hG q hq hqu
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  have hs : MeasurableSet (bBall k r ρ) := measurableSet_expBall k r (UWb k r) ρ
  have hu := uwb_unit hq
  have hqi : q⁻¹ = qᴴ := Matrix.inv_eq_left_inv hqu
  have hq' : qᴴ ∈ UWb k r := by rw [← hqi]; exact uwb_inv hq
  have hqu' : (qᴴ)ᴴ * qᴴ = 1 := by rw [conjTranspose_conjTranspose, ← hqi, Matrix.mul_nonsing_inv _ hu]
  have le1 : ∀ q : Mat k r, q ∈ UWb k r → qᴴ * q = 1 → ν.map (rmulM q) (bBall k r ρ) ≤ ν (bBall k r ρ) := by
    intro q hq hqu
    rw [Measure.map_apply (rmulM_meas q) hs]
    calc ν (rmulM q ⁻¹' bBall k r ρ) ≤ ν (lmulM q ⁻¹' bBall k r ρ) := measure_mono (hB k r ρ q hq hqu)
      _ = ν.map (lmulM q) (bBall k r ρ) := (Measure.map_apply (lmulM_cont q).measurable hs).symm
      _ = ν (bBall k r ρ) := by rw [hG.1.2.2.2 q hq]
  have hsc := rmul_scale ν hG.1 q hq _ h0.ne' ht.ne
  have hsc' := rmul_scale ν hG.1 qᴴ hq' _ h0.ne' ht.ne
  have hm := scale_mul_one ν q qᴴ (by rw [← hqi, Matrix.mul_nonsing_inv _ hu]) _ h0.ne' ht.ne _ _ hsc hsc'
  have hc1 : ν.map (rmulM q) (bBall k r ρ) / ν (bBall k r ρ) ≤ 1 :=
    (ENNReal.div_le_iff h0.ne' ht.ne).2 (by rw [one_mul]; exact le1 q hq hqu)
  have hc1' : ν.map (rmulM qᴴ) (bBall k r ρ) / ν (bBall k r ρ) ≤ 1 :=
    (ENNReal.div_le_iff h0.ne' ht.ne).2 (by rw [one_mul]; exact le1 qᴴ hq' hqu')
  rw [hsc, one_of_le _ _ hm hc1 hc1', one_smul]

theorem hb_sq (k : ℕ) : Hb k * Hb k = 1 := by
  rw [Hb, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; split_ifs <;> norm_num

theorem hermInv_of (hU : UnitInv) : HermInv := by
  intro k r ν hk hG B₀ hB hBh
  have hHbh : (Hb k)ᴴ = Hb k := MB.Hb_conjT
  have hE : embWb k r (Hb k) ∈ UWb k r := MB.emb_mem_UWb (by rw [hHbh, hb_sq, Matrix.one_mul])
  have hEu : (embWb k r (Hb k))ᴴ * embWb k r (Hb k) = 1 := by
    rw [MB.emb_conjT, hHbh, ← MB.emb_mul, hb_sq, MB.emb_one]
  have hBm : embWb k r B₀ ∈ UWb k r := MB.emb_mem_UWb hB
  have hinv : embWb k r B₀ * (embWb k r (Hb k) * embWb k r B₀ * embWb k r (Hb k)) = 1 := by
    rw [← MB.emb_mul, ← MB.emb_mul, ← MB.emb_mul]
    have : B₀ * (Hb k * B₀ * Hb k) = 1 := by
      calc B₀ * (Hb k * B₀ * Hb k) = (B₀ᴴ * Hb k * B₀) * Hb k := by rw [hBh]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hB, hb_sq]
    rw [this, MB.emb_one]
  have hEinv := hU k r ν hk hG _ hE hEu
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  have hsc := rmul_scale ν hG.1 _ hBm _ h0.ne' ht.ne
  set c := ν.map (rmulM (embWb k r B₀)) (bBall k r ρ) / ν (bBall k r ρ) with hc
  have h2 : ν.map (rmulM (embWb k r (Hb k) * embWb k r B₀ * embWb k r (Hb k))) = c • ν := by
    rw [← rmulM_comp, ← rmulM_comp, ← Measure.map_map (rmulM_meas _) ((rmulM_meas _).comp (rmulM_meas _)),
      ← Measure.map_map (rmulM_meas _) (rmulM_meas _), hEinv, hsc, Measure.map_smul, hEinv]
  have hcc := scale_mul_one ν _ _ hinv _ h0.ne' ht.ne c c hsc h2
  rw [hsc, one_of_sq c hcc, one_smul]

theorem unimodW_of_two (hB : BallConj) (hP : PolarDecW) : UnimodW :=
  unimodW_of (unitInv_of hB) (hermInv_of (unitInv_of hB)) hP

end PI.RhsWLim.W
