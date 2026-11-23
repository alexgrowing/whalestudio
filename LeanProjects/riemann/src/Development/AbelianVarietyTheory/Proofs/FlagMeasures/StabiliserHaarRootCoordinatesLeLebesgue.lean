import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordConjEqStCoord
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlockStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreimageReindexScaleComplexLeStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.LoopVol

theorem pinned_ratCoord_le : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γw sf : X.B.I.Ginf) (μw : MeasureTheory.Measure X.B.I.Ginf), IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw → μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w → D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 → ∀ A : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet A → (μw.map (fun y => sf * y * sf⁻¹)) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro D X u u' w γw sf μw _hH hmap hc A hA
  classical

  let ι : GlobalTheory.LoopV.roots (ptMat w) ≃ Formalism.L2.SG.RealObj.FreeE w :=
    Equiv.subtypeEquivRight (fun p => GlobalTheory.T.mem_roots_point_matrix_iff_same_block D.host.E (D.R.rS + 1) w p.1 p.2)
  let d : GlobalTheory.LoopV.roots (ptMat w) → ℕ := fun q => q.1.2.1 - q.1.1.1
  let S : (NumberField.InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) :=
    fun x τ q => (((D.host.rdE : ℝ) : ℂ) ^ d q)⁻¹ * x (X.pl.symm τ) (ι q)
  have hS : Continuous S := by
    refine continuous_pi fun τ => continuous_pi fun q => continuous_const.mul ?_
    exact (continuous_apply _).comp (continuous_apply _)
  have hΦ : Continuous (fun y : X.B.I.Ginf => sf * y * sf⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hst := Formalism.L2.SG.Pf.LoopBPin.stCoord_cont (X := X) u' w γw
  have hrat := ratCoord_cont X u' w γw sf
  have hpre : (fun y : X.B.I.Ginf => sf * y * sf⁻¹) ⁻¹' (ratCoord X u' w γw sf ⁻¹' A) =
      Formalism.L2.SG.RealObj.stCoord X u' w γw ⁻¹' (S ⁻¹' A) := by
    ext y
    simp only [Set.mem_preimage]
    have : ratCoord X u' w γw sf (sf * y * sf⁻¹) = S (Formalism.L2.SG.RealObj.stCoord X u' w γw y) := by
      funext τ q
      exact ratCoord_conj_eq_stCoord D X u' w γw sf y τ q (ι q) rfl
    rw [this]
  have hB : MeasurableSet (S ⁻¹' A) := hS.measurable hA
  rw [Measure.map_apply hΦ.measurable (hrat.measurable hA), hpre,
    ← Measure.map_apply hst.measurable hB, hmap]
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE (D := D)
  have key := GlobalTheory.T.measure_preimage_reindex_scale_complex_le D.what₂.Tau (NumberField.InfinitePlace X.B.I.F) (GlobalTheory.LoopV.roots (ptMat w)) (Formalism.L2.SG.RealObj.FreeE w)
    X.pl.symm ι D.host.rdE (D.host.ka / (X.B.g : ℝ) / Real.pi) d hrd hc A hA
  refine le_trans key ?_
  gcongr
  · rw [D.what₂.card_Tau]
  · have hsum : ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ (D.R.rS + 1) ^ 3 := by
      calc ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ ∑ _q : GlobalTheory.LoopV.roots (ptMat w), (D.R.rS + 1) :=
            Finset.sum_le_sum fun q _ => by
              have := q.1.2.2; simp only [d]; omega
        _ = Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) * (D.R.rS + 1) := by simp
        _ ≤ (D.R.rS + 1) ^ 2 * (D.R.rS + 1) := by
            gcongr
            calc Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) ≤ Fintype.card (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :=
                  Fintype.card_subtype_le _
              _ = (D.R.rS + 1) ^ 2 := by simp [sq]
        _ = (D.R.rS + 1) ^ 3 := by ring
    exact hsum

end GlobalTheory.LoopVol
