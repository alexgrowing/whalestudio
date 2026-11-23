import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserRationalUnitriangularPairsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularStabilizerPointMatrixBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFrameStabilizerActsUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserEqOneOfFixesSecondFrameStatement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StCoord

theorem zh_eq (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k)
    (c : GCoord Z F0 F0' FP G) : G.Zh = ZhatL F0 F0' := by
  have hs : ∀ x : D.host.E, D.conjF x = star x := fun x => by
    rw [D.conjF_eq]; exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  funext a b
  have := c.h_eq (frame F0' b) (frame F0 a)
  simp only [GFrames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq]
  simp only [hs]
  exact this

theorem stab_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), (∀ x ∈ G.St, ∃ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B ∧ (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) ∧ ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) ∧ ∀ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B → (∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) → ∃! x, x ∈ G.St ∧ ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a := by
  intro D X Y u u' _ _ w F00 F'0 FP hw _ _ G c
  have hZ : Formalism.MainNotions.S.ZhatOM G.Zh = Formalism.MainNotions.S.ptMat w := by rw [zh_eq D _ F00 F'0 FP G c]; exact hw
  have hinv : ∀ x, (D.conjF : D.host.E →+* D.host.E) ((D.conjF : D.host.E →+* D.host.E) x) = x := by
    intro x
    have hs : ∀ x : D.host.E, D.conjF x = star x := fun x => by
      rw [D.conjF_eq]; exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
    show D.conjF (D.conjF x) = x
    rw [hs, hs, star_star]
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.unitriangularStabilizer_pointMatrix_blockDiagonal (D.conjF : D.host.E →+* D.host.E) hinv D.R.rS w G.Zh hZ
  have up : ∀ s : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ↔ Formalism.MainNotions.S.IsUpUni s := by
    intro s
    constructor
    · rintro ⟨h1, h2⟩ i j; exact ⟨h1 i j, fun h => h ▸ h2 i⟩
    · intro h; exact ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩
  refine ⟨fun x hx => ?_, fun B hB hBb => ?_⟩
  · obtain ⟨s, s', hs, hs', hf, hf'⟩ := GlobalTheory.T.globalFrameStabilizer_acts_unitriangular _ _ _ G x hx
    have hZs := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs _ _ _ G s s' hs hs').2 ⟨x, hx, hf, hf'⟩
    exact ⟨s', (up s').1 hs', hf', hb1 s s' ((up s).1 hs) ((up s').1 hs') hZs⟩
  · obtain ⟨s, hs, hZs⟩ := hb2 B hB hBb
    obtain ⟨h, hh, -, hh'⟩ := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs _ _ _ G s B ((up s).2 hs) ((up B).2 hB)).1 hZs
    refine ⟨h, ⟨hh, hh'⟩, fun y ⟨hy, hy'⟩ => ?_⟩
    have h1 : h⁻¹ * y = 1 := by
      refine GlobalTheory.T.rationalCommonStabiliser_eq_one_of_fixes_second_frame _ _ _ G _ (G.St.mul_mem (G.St.inv_mem hh) hy) fun b => ?_
      show h.symm (y (G.f' b)) = G.f' b
      rw [hy', ← hh' b, LinearEquiv.symm_apply_apply]
    calc y = h * (h⁻¹ * y) := by group
      _ = h := by rw [h1, mul_one]

end GlobalTheory.HL.StCoord
