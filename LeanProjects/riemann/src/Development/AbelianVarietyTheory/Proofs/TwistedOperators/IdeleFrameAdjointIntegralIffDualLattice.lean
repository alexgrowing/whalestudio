import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HformZeroRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatAStdLIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.DualRed

theorem adjA_entry : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO S T) (k : Fin S.rank) (j : Fin T.rank), adjA S T βS βT 1 x k j = Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (T.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (fun c => toEAf D (x c k)) (fun c => βT.1 c j) := by
  intro D S T hS βS βT x k j
  have hE : toEAf D = GlobalTheory.LevSplit.finSw D := rfl
  unfold adjA frMapAdj
  rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, map_one, one_smul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.map_mul]
  unfold Formalism.UG.hform
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, hE, GlobalTheory.LevSplit.finSw_cA,
    GlobalTheory.LevSplit.finSw_incA, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem adj_int_iff : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βT ΛT → ∀ (J : Ideal (𝓞 D.host.E)), Squarefree J → ∀ x : WO S T, IsFinPt x → ((IsIntM (adjA S T βS βT 1 x) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E, J ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 x) = 0) ↔ x ∈ hatA S T (tens (stdL D.host.E S.rank) (conjI J • ΛT))) := by
  intro D S T hS ΛT hsd βS βT hfr J hJ x hx
  have hJ0 : J ≠ ⊥ := by
    rw [← Submodule.zero_eq_bot]
    exact hJ.ne_zero
  rw [GlobalTheory.TensColRead.mem_hatA_stdL_iff D S T _ x hx]
  simp only [GlobalTheory.FrameIdeal.mem_hatL_conjI_iff_hform D T ΛT hsd βT hfr J hJ0, ← adjA_entry D S T hS βS βT x]
  unfold IsIntM redM
  constructor
  · rintro ⟨hint, hred⟩ k j
    refine ⟨⟨_, hint k j⟩, GlobalTheory.LiftLevel.mem_idS hJ fun PP hPP => ?_, rfl⟩
    have h0 := congrFun (congrFun (hred PP hPP) k) j
    simpa only [Matrix.zero_apply, Pi.zero_apply, dif_pos (hint k j)] using h0
  · intro h
    have hint : ∀ k j, adjA S T βS βT 1 x k j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro k j
      obtain ⟨s, -, hs⟩ := h k j
      rw [← hs]
      exact s.2
    refine ⟨hint, fun PP hPP => ?_⟩
    funext k j
    obtain ⟨s, hsI, hs⟩ := h k j
    have hse : (⟨adjA S T βS βT 1 x k j, hint k j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = s := Subtype.ext hs.symm
    simp only [Matrix.zero_apply, Pi.zero_apply, dif_pos (hint k j), hse]
    exact GlobalTheory.LiftLevel.resS_eq_zero hPP hsI

end GlobalTheory.DualRed
