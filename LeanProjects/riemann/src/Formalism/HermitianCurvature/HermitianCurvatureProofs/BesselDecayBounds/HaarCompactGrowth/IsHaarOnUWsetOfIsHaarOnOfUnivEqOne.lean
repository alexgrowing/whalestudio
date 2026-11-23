import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.ExpUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.LieNUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.PeriodIntegrals.BesselPeriodGGP
import Formalism.PeriodIntegrals.IsLowUnitH

open MeasureTheory Matrix
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.MeasFS

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def NLeft : Prop :=
  ∀ (k r : ℕ) (κ : ℝ≥0∞), κ ≠ 0 → κ ≠ ⊤ → ∀ a ∈ Nset k r,
    (Formalism.MainNotions.S.haarLie (Nset k r) κ).map (lmulM a) = Formalism.MainNotions.S.haarLie (Nset k r) κ

theorem conj_meas (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (conjM (k := k) (r := r) a) := by
  refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Formalism.QuantumDeterminants.conjM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ =>
    (continuous_finset_sum _ fun n _ => by fun_prop).mul continuous_const

theorem rmul_meas (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (Formalism.FourierDecayAlt.B.rmulF a : Mt k r → Mt k r) := by
  refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Formalism.FourierDecayAlt.B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ => by fun_prop

theorem isHaarOn_UWset_of_isHaarOn_of_univ_eq_one {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hμ : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (h1 : μW Set.univ = 1) :
    Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW := by
  have : IsFiniteMeasure μW := ⟨by rw [h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (UWset k r z) μ0 μW
    (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) h0 hμ.2.2.1 hμ.2.2.2 (fun K _ => measure_lt_top _ _)
  refine ⟨hμ.2.2.1, hμ.2.2.2, fun a ha => ?_, fun K _ => measure_lt_top _ _, hμ.2.1⟩
  rw [hc, Measure.map_smul, h0.right a ha]

theorem measPresW_right {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)} (hz : inWb k r z)
    (hT : 0 < Tz k r z) (hμ : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (h1 : μW Set.univ = 1) :
    ∀ h ∈ UWset k r z, MeasurePreserving (fun x : Mt k r => fun i j => (Matrix.of x * h) i j) μW μW :=
  fun h hh => ⟨rmul_meas h, (isHaarOn_UWset_of_isHaarOn_of_univ_eq_one hz hT hμ h1).right h hh⟩

theorem hsN_cont : Continuous (fun y : Mt k r => Formalism.MainNotions.GrowthW.hsN (Matrix.of y)) := by
  unfold Formalism.MainNotions.GrowthW.hsN
  simp only [Matrix.of_apply]
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem haarLie_finite_compact (κ : ℝ≥0∞) (hκ : κ ≠ ⊤) (K : Set (Mt k r)) (hK : IsCompact K) :
    Formalism.MainNotions.S.haarLie (Nset k r) κ K < ⊤ := by
  obtain ⟨C, D, hD, hCD⟩ := Formalism.MainNotions.GrowthW.expUpper (2 * r + k + 1) (by omega)
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (hsN_cont (k := k) (r := r)).continuousOn
  have hsub : (fun x : Formalism.MainNotions.S.lieE (Nset k r) =>
      (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify
        (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j : Mt k r)) ⁻¹' K ⊆
      Metric.closedBall 0 (|C| * R ^ D) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    set X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
      Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) with hXdef
    have hX : Formalism.MainNotions.GrowthW.SUpper X := Formalism.MainNotions.GrowthW.lieNUpper k r X (PI.WUN.lieN_of_lieE _ x.2)
    have h1 := hCD X hX
    have hx0 : ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ ≤
        Formalism.MainNotions.GrowthW.hsN X := Formalism.MainNotions.GrowthW.norm_le_hsN (k := k) (r := r) _
    have hxx : ‖x‖ = ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ := rfl
    have hb0 := hR _ hx
    have he : Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X) ≤ R := by
      have e1 : Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X) ≤ ‖Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X)‖ := by
        rw [Real.norm_eq_abs]; exact le_abs_self _
      exact e1.trans hb0
    have he0 : 0 ≤ Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X) := Formalism.MainNotions.GrowthW.hsN_nonneg _
    have hX0 : 0 ≤ Formalism.MainNotions.GrowthW.hsN X := Formalism.MainNotions.GrowthW.hsN_nonneg _
    have hp : Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X) ^ D ≤ R ^ D := Real.rpow_le_rpow he0 he hD.le
    have hp0 : 0 ≤ Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X) ^ D := Real.rpow_nonneg he0 D
    have hc1 : C * Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X) ^ D ≤ |C| * Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X) ^ D :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hp0
    have hc2 : |C| * Formalism.MainNotions.GrowthW.hsN (NormedSpace.exp X) ^ D ≤ |C| * R ^ D :=
      mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    rw [hxx]
    linarith
  unfold Formalism.MainNotions.S.haarLie
  rw [Measure.smul_apply, Measure.map_apply (PI.WUN.continuous_expLie (Nset k r)).measurable hK.measurableSet,
    smul_eq_mul]
  exact ENNReal.mul_lt_top hκ.lt_top ((measure_mono hsub).trans_lt measure_closedBall_lt_top)

theorem haarLie_ne_zero (κ : ℝ≥0∞) (h0 : κ ≠ 0) : Formalism.MainNotions.S.haarLie (Nset k r) κ ≠ 0 := by
  intro h
  have h2 : Formalism.MainNotions.S.haarLie (Nset k r) κ Set.univ = 0 := by rw [h]; simp
  unfold Formalism.MainNotions.S.haarLie at h2
  rw [Measure.smul_apply, Measure.map_apply (PI.WUN.continuous_expLie (Nset k r)).measurable MeasurableSet.univ,
    Set.preimage_univ, smul_eq_mul, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact h0 h2
  · exact (MeasureTheory.Measure.IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty) h2

theorem haar_lie_measure_on_nilpotent (hL : NLeft) (κ : ℝ≥0∞) (h0 : κ ≠ 0) (hκ : κ ≠ ⊤) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) κ) := by
  have hconc : Formalism.MainNotions.S.haarLie (Nset k r) κ (Nset k r)ᶜ = 0 := PI.WUN.muN_conc κ
  have hleft := hL k r κ h0 hκ
  have hfin := haarLie_finite_compact (k := k) (r := r) κ hκ
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Nset k r) μ0 _ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hμ0
    hconc hleft hfin
  refine ⟨hconc, hleft, fun a ha => ?_, hfin, haarLie_ne_zero κ h0⟩
  rw [hc, Measure.map_smul, hμ0.right a ha]

theorem measPresN_conj_of {z : Fin (2 * r + k + 1) → ℂ} {μN : Measure (Mt k r)}
    (hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r,
      MeasurePreserving (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m) i j) μN μN := by
  intro h hh m hm
  have hdet : IsUnit h.det := PI.WUN.UH_det hh.1
  have hhi : h⁻¹ ∈ UWset k r z := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z).inv_mem h hh
  have hC : MeasurePreserving (conjM (k := k) (r := r) h⁻¹) μN μN :=
    ⟨conj_meas h⁻¹, Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z _ hz hT hN h⁻¹ hhi⟩
  have hR : MeasurePreserving (Formalism.FourierDecayAlt.B.rmulF m : Mt k r → Mt k r) μN μN :=
    ⟨rmul_meas m, hN.right m hm⟩
  have e : (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m) i j) =
      (Formalism.FourierDecayAlt.B.rmulF m : Mt k r → Mt k r) ∘ conjM (k := k) (r := r) h⁻¹ := by
    funext x
    exact (congrArg (fun t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      (fun i j => (h⁻¹ * Matrix.of x * t * m) i j : Mt k r)) (Matrix.nonsing_inv_nonsing_inv h hdet)).symm
  rw [e]
  exact hR.comp hC

theorem measPresN_inv_of {z : Fin (2 * r + k + 1) → ℂ} {μN : Measure (Mt k r)}
    (hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∀ h ∈ UWset k r z,
      MeasurePreserving (fun x : Mt k r => fun i j => (h * (Matrix.of x)⁻¹ * h⁻¹) i j) μN μN := by
  intro h hh
  have hC : MeasurePreserving (conjM (k := k) (r := r) h) μN μN :=
    ⟨conj_meas h, Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z _ hz hT hN h hh⟩
  have hI : MeasurePreserving (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) μN μN :=
    ⟨PI.WBL.Cv.measurable_matInv, Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) _
      (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN⟩
  exact hC.comp hI

theorem measF_side {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {μW μN : Measure (Mt k r)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW) (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    PI.WBL.Cv.MeasF z π μW μN := by
  have hW' : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW := ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2⟩
  have hN' : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN := ⟨hN.1, hN.2.1, hN.2.2.1, hN.2.2.2⟩
  have hWc := Formalism.MainNotions.BridgeLemma₃.hu_haarUp.1 k r z μW hz hT hW'
  have hNc := Formalism.MainNotions.BridgeLemma₃.hu_haarUp.2 k r μN hN'
  haveI : SigmaFinite μW := hW.1
  haveI : SigmaFinite μN := hN.1
  exact PI.WBL.Cv.measF_of (fun h hh => ⟨rmul_meas h, hWc.right h hh⟩)
    ⟨PI.WBL.Cv.measurable_matInv, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hWc⟩
    hW.2.2.1 hN.2.2.1 (measPresN_conj_of hNc hz hT) (measPresN_inv_of hNc hz hT)
    (PI.WBL.Cv.piContAll k r z u Wp π hz hT hπ)

end Formalism.MainNotions.MeasFS
