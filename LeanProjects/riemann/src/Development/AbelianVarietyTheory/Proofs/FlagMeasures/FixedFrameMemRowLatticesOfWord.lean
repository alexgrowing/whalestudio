import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowFrame

theorem ddIdeal_ne_bot (D : D7) :
    (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) : Ideal (𝓞 D.host.E)) ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem one_mem_ddS_zpow_neg (D : D7) (m : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [zpow_neg, zpow_natCast, ddS, ← FractionalIdeal.coeIdeal_pow]
  refine FractionalIdeal.one_mem_inv_coe_ideal ?_
  rw [← Ideal.zero_eq_bot]
  exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact ddIdeal_ne_bot D)

theorem frame_mem_rowLat (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a ∈ Λ := by
  obtain ⟨-, ⟨-, -, hz, -⟩, hX⟩ := hΛ
  have hXS : XS D F0 ≤ Λ := by
    rw [← hX]; exact inf_le_left
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => (VS D).V) F0.e F0.z (Fin.last _) ∈ Λ
    rw [Fin.snoc_last]; exact hz.1
  | cast i =>
    show Fin.snoc (α := fun _ => (VS D).V) F0.e F0.z i.castSucc ∈ Λ
    rw [Fin.snoc_castSucc]
    apply hXS
    apply Submodule.subset_span
    refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
    have : -((D.R.rS : ℤ) - ((i : ℕ) : ℤ)) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub i.isLt.le]
    rw [this]
    exact one_mem_ddS_zpow_neg D _

theorem frame_mem_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    Λ ∈ Y.what₂ u → ∀ a, frame (lf D (X.Fu u)) a ∈ Λ :=
  fun D X Y u Λ hΛ a => frame_mem_rowLat D (X.Fu u) Λ ((Y.rowsOK u).1 Λ hΛ) a

end GlobalTheory.RowFrame
