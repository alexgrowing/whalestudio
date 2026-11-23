import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RhoTieCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LiftMassCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem autLz_nonempty {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (autLz D F0 Λ).Nonempty := by
  have h1 : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := ⟨one_mem _, fun j => kmap_one _, rfl⟩
  exact ⟨ind F0 h1, (autLz_iff F0 Λ _).2 ⟨1, h1, gmap_one' Λ, rfl⟩⟩

theorem massRows_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
  have hne : (Y.what₂ u).Nonempty := ⟨_, (cls_spec (Y.rowsOK u) (latRowLat X u) 1).1⟩
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_pos (fun Λ hΛ => ?_) hne
  haveI := Formalism.L2.SG.Pf.FibreCounting.autLz_finite (Y := Y) (Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) hΛ
  have hpos : 0 < Nat.card ↥(autLz D (X.Fu u) Λ) := by
    obtain ⟨φ, hφ⟩ := autLz_nonempty (X.Fu u) Λ
    haveI : Nonempty ↥(autLz D (X.Fu u) Λ) := ⟨⟨φ, hφ⟩⟩
    exact Nat.card_pos
  unfold Formalism.MainNotions.S.wRow
  exact inv_pos.2 (Nat.cast_pos.2 hpos)

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_closed {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  RhoTieC_holds X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.latRowLat X u) (Formalism.L2.SG.Pf.latInj X u)
    (Formalism.L2.SG.Pf.latSurj X u)

end Formalism.L2.SG.MassDataConc
