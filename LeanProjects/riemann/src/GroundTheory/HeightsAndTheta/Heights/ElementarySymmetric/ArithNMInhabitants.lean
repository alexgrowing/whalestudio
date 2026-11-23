import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StArithNMSmallSection
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StArithNMLift
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StAmpleOnModelRestrict
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NMPointZero

def line : Geo.HermLine (blockIdx fun _ : Unit ↦ 0) where
  a := 0
  h _ := 2
  pos _ _ := two_pos
  smul c z hc := by simp

theorem isSemipositiveRel (P0 P : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) :
    Geo.IsSemipositiveRel P0 P line := by
  refine ⟨contDiffOn_const, fun z _ w _ => ?_⟩
  simp [line, Geo.leviForm]

theorem isAmpleOnModel : IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint line.a := by
  intro e
  refine ⟨0, fun n _ => ⟨1, fun _ => 1, fun _ c _ => ?_, fun c _ => ⟨fun _ => 1, fun _ => one_mem _, ?_⟩⟩⟩
  · simp [unitPoint]
  · simp [unitPoint]

theorem isBoundedH_one :
    IsBoundedH (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) unitPoint
      (GroundTheory.Heights₂.Heights.Inter.hermZpow line ((1 : ℕ) : ℤ)) 1 (1 / 2) 1 := by
  intro dg dh g h z hg hh hd he _
  have hdd : dg = dh := by
    funext k
    have h1 := hd k
    simp [GroundTheory.Heights₂.Heights.Inter.hermZpow, line] at h1
    exact_mod_cast h1
  subst hdd
  have hgh : g - h = 0 := by
    refine form_eq_zero_of_unitPoint (δ := dg) ?_ ?_
    · exact ((geoMultiHomog_iff g dg).mp hg).sub ((geoMultiHomog_iff h dg).mp hh)
    · rw [map_sub, he, one_mul, sub_self]
  rw [sub_eq_zero.mp hgh]
  simp [GroundTheory.Heights₂.Heights.Inter.hermZpow, line]
  linarith [norm_nonneg (eval z (map (Int.castRingHom ℂ) h))]

def oneSystem : Geo.IntersectionSystem := fun _ _ _ _ _ _ _ => 1

end NMPointZero

theorem ArithNMLift.hyps_inhabited :
    Geo.IsArithVar (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) ∧
      (⊥ : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) ≤ Geo.mCoordIdeal unitPoint ∧
      Geo.IsSemipositiveRel ⊥ (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) NMPointZero.line ∧
      Geo.IsConjInvariantH NMPointZero.line ∧
      IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint NMPointZero.line.a ∧
      (∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ Geo.chartLat (ι := blockIdx fun _ : Unit ↦ 0) unitPoint
          (GroundTheory.Heights₂.Heights.Inter.hermZpow NMPointZero.line m).a 1, s ≠ 0 ∧
        ∃ c : ℝ, c < 1 ∧ IsBoundedH (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) unitPoint
          (GroundTheory.Heights₂.Heights.Inter.hermZpow NMPointZero.line m) 1 c s) ∧
      (∀ (W : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) (e : ℕ), Geo.IsArithVar W (e + 1) →
        Geo.mCoordIdeal unitPoint ≤ W → e < 0 →
        ∀ (Ω' : Type) [Field Ω'] (y' : (Σ k, (blockIdx fun _ : Unit ↦ 0) k) → Ω'),
          Geo.mCoordIdeal y' = W → IsGenBySmallSections y' NMPointZero.line) := by
  refine ⟨unitPoint_isArithVar, bot_le, NMPointZero.isSemipositiveRel _ _, fun _ => rfl, NMPointZero.isAmpleOnModel,
    ⟨1, le_rfl, 1, fun c _ => ?_, one_ne_zero, 1 / 2, by norm_num, NMPointZero.isBoundedH_one⟩,
    fun _ e _ _ he => absurd he (Nat.not_lt_zero e)⟩
  simp [unitPoint]

theorem ArithNMSmallSection.hyps_inhabited :
    Geo.IsArithVar (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) ∧
      (⊥ : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) ≤ Geo.mCoordIdeal unitPoint ∧
      Geo.IsSemipositiveRel ⊥ (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) NMPointZero.line ∧
      Geo.IsConjInvariantH NMPointZero.line ∧
      IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint NMPointZero.line.a ∧
      0 < NMPointZero.oneSystem Unit (blockIdx fun _ : Unit ↦ 0)
        (Geo.mCoordIdeal unitPoint) (0 + 1) (fun _ => NMPointZero.line) :=
  ⟨unitPoint_isArithVar, bot_le, NMPointZero.isSemipositiveRel _ _, fun _ => rfl, NMPointZero.isAmpleOnModel,
    one_pos⟩

theorem AmpleOnModelRestrict.hyps_inhabited :
    Geo.mCoordIdeal (ι := ArakelovGeometry.GlobalTheory (Fin 2)) ProjLine.y ≤ Geo.mCoordIdeal (ι := ArakelovGeometry.GlobalTheory (Fin 2)) (fun _ => (1 : ℚ)) ∧
      IsAmpleOnModel (ι := ArakelovGeometry.GlobalTheory (Fin 2)) ProjLine.y ProjLine.fsLine1.a :=
  ⟨by rw [ProjLine.mCoordIdeal_y]; exact bot_le, isAmpleOnModel_projLine⟩

end

end GroundTheory.Heights₂.Heights.Targets
