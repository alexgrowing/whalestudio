import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000

namespace GlobalTheory.BKLim.SatLat

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk τ hτ d N T0 V V' Y1 hT0 hV hV' hVV' hY1
  classical
  obtain ⟨htu, -, -, -⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  have hOEcl := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (WCb l), M = inclW l τ ^ N • T0 := ⟨_, rfl⟩
  have hMu : IsUnit M.det := by
    rw [hM, Matrix.det_smul]
    exact ((htu.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det T0).1 hT0)
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hVu : IsUnit V.det := by
    have h : V.det * V'.det = 1 := by rw [← Matrix.det_mul, hVV', Matrix.det_one]
    exact ⟨⟨V.det, V'.det, h, by rw [mul_comm]; exact h⟩, rfl⟩
  let ι : (Fin d → Ainf l) → (Fin d → WCb l) := fun y a => inclW l (y a)
  have hιmul : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (v : Fin d → Ainf l),
      ι (A *ᵥ v) = A.map (inclW l) *ᵥ ι v := by
    intro A v; funext i; simp [ι, Matrix.mulVec, dotProduct, map_sum]
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have hevWι : ∀ c : Fin d → bk.S, ι (fun a => bk.ev (c a)) = fun a => bk.evW (c a) := fun c => rfl
  let mem : (Fin d → Ainf l) → Prop := fun y => ∀ i, (M⁻¹ *ᵥ ι y) i ∈ bk.OE
  have hY1M : Y1.map (inclW l) = M * V := by rw [hY1, hM, Matrix.smul_mul]
  have hmemV : ∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a)) := by
    intro c i
    show (M⁻¹ *ᵥ ι (Y1 *ᵥ fun a => bk.ev (c a))) i ∈ bk.OE
    rw [hιmul, hevWι, hY1M, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hMM', Matrix.one_mul]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hV i j) (hevW _)
  obtain ⟨Y, hYu, hYmem⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d mem
    (fun i => by
      show (M⁻¹ *ᵥ ι 0) i ∈ bk.OE
      have : ι 0 = 0 := by funext a; simp [ι]
      rw [this, Matrix.mulVec_zero]; exact Subring.zero_mem _)
    (fun y z hy hz i => by
      show (M⁻¹ *ᵥ ι (y + z)) i ∈ bk.OE
      have : ι (y + z) = ι y + ι z := by funext a; simp [ι]
      rw [this, Matrix.mulVec_add]; exact Subring.add_mem _ (hy i) (hz i))
    (fun c y hy i => by
      show (M⁻¹ *ᵥ ι (fun a => bk.ev c * y a)) i ∈ bk.OE
      have : ι (fun a => bk.ev c * y a) = bk.evW c • ι y := by funext a; simp [ι, BK.evW]
      rw [this, Matrix.mulVec_smul]; exact Subring.mul_mem _ (hevW c) (hy i))
    (fun y hy i => by
      have h : (M⁻¹ *ᵥ ι (fun a => (l : Ainf l) * y a)) i ∈ bk.OE := hy i
      have : ι (fun a => (l : Ainf l) * y a) = ((l : ℕ) : WCb l) • ι y := by funext a; simp [ι]
      rw [this, Matrix.mulVec_smul] at h
      exact hOEcl.1 _ h)
    (fun y hy _ z hz i => by
      refine hOEcl.2.1 _ fun n => ⟨_, hy n i, ?_⟩
      rw [← Pi.sub_apply, ← Matrix.mulVec_sub]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
      have := map_dvd (inclW l) (hz n j)
      simpa [ι, map_sub, map_pow, map_natCast] using this)
    Y1 M (by rw [hY1M, Matrix.det_mul]; exact (hMu.mul hVu).ne_zero)
    ((Matrix.isUnit_iff_isUnit_det M).2 hMu) hmemV
    (fun y hy => by
      refine ⟨M⁻¹ *ᵥ ι y, hy, ?_⟩
      show ι y = M *ᵥ (M⁻¹ *ᵥ ι y)
      rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec])
  obtain ⟨Wm, hWm⟩ : ∃ Wm : Matrix (Fin d) (Fin d) (WCb l), Wm = M⁻¹ * Y.map (inclW l) := ⟨_, rfl⟩
  have hYWm : Y.map (inclW l) = M * Wm := by rw [hWm, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  have hcol : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (j : Fin d),
      (A *ᵥ fun a => bk.ev ((Pi.single j (1 : bk.S) : Fin d → bk.S) a)) = fun i => A i j := by
    intro A j; funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hWmOE : ∀ i j, Wm i j ∈ bk.OE := by
    intro i j
    have h : (M⁻¹ *ᵥ ι (fun a => Y a j)) i ∈ bk.OE := (hYmem (fun a => Y a j)).2 ⟨Pi.single j (1 : bk.S), (hcol Y j).symm⟩ i
    rw [hWm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, ι] using h
  have hC : ∀ j, ∃ c : Fin d → bk.S, (fun i => Y1 i j) = Y *ᵥ fun a => bk.ev (c a) := fun j =>
    (hYmem _).1 (by rw [← hcol Y1 j]; exact hmemV _)
  choose c hc using hC
  obtain ⟨Cw, hCw⟩ : ∃ Cw : Matrix (Fin d) (Fin d) (WCb l), Cw = Matrix.of fun a j => bk.evW (c j a) := ⟨_, rfl⟩
  have hVW : V = Wm * Cw := by
    have h1 : Y1.map (inclW l) = Y.map (inclW l) * Cw := by
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun v => inclW l (v i)) (hc j)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hCw, BK.evW, map_sum] using this
    rw [hY1M, hYWm, Matrix.mul_assoc] at h1
    have h2 := congrArg (HMul.hMul M⁻¹) h1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMM', Matrix.one_mul, Matrix.one_mul] at h2
    exact h2
  refine ⟨Y, Wm, Cw * V', hYu, hWmOE, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, hCw, Matrix.of_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hevW _) (hV' k j)
  · rw [← Matrix.mul_assoc, ← hVW, hVV']
  · rw [hYWm, hM, Matrix.smul_mul]
  · rintro y ⟨w, hw, hyw⟩
    refine (hYmem y).1 ?_
    intro i
    have : ι y = M *ᵥ w := by
      rw [hM]; refine hyw.trans ?_; funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    show (M⁻¹ *ᵥ ι y) i ∈ bk.OE
    rw [this, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]; exact hw i

end GlobalTheory.BKLim.SatLat
