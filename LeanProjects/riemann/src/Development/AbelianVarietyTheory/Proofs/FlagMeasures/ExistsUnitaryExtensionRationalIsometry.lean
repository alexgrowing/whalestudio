import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

theorem form_ext_left {D : D7} (Z : LocDat D) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (w w' : Vp D p)
    (h : ∀ x, (locH Z p).h (g (baseChange₂ D p x)) w' = (locH Z p).h (baseChange₂ D p x) w) (x : Vp D p) :
    (locH Z p).h (g x) w' = (locH Z p).h x w := by

  have hx : x ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by
    rw [span_baseChange_eq_top p]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    exact h z
  | zero =>
    rw [map_zero, (locH Z p).h_zero_left, (locH Z p).h_zero_left]
  | add y y' _ _ hy hy' =>
    rw [map_add, (locH Z p).h_add_left, (locH Z p).h_add_left, hy, hy']
  | smul a y _ hy =>
    rw [map_smul, (locH Z p).h_smul_left, (locH Z p).h_smul_left, hy]

theorem exists_ext_unitary : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), ρ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ∃ g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p, GlobalTheory.LocOver.Ext p ρ g ∧ Formalism.MainNotions.S.LocNG.IsUnitary (locH Z p) g := by
  intro D Z p ρ hρ

  obtain ⟨g, hg⟩ := GlobalTheory.HL.RatExt.exists_equiv (D.s.atP p).ιE
    ((VS D).frame.equivFun.symm.trans (ρ.trans (VS D).frame.equivFun))
  have hext : GlobalTheory.LocOver.Ext p ρ g := by
    intro x
    have h1 := hg ((VS D).frame.equivFun x)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h1
    exact h1
  have hρ' : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ

  have hA : ∀ a b, (locH Z p).h (g (baseChange₂ D p a)) (g (baseChange₂ D p b)) =
      (locH Z p).h (baseChange₂ D p a) (baseChange₂ D p b) := by
    intro a b
    rw [hext a, hext b]
    show LocFacts₂ Z.M p _ _ = LocFacts₂ Z.M p _ _
    rw [baseChangeAt_form Z.M p (Z.hcj p), baseChangeAt_form Z.M p (Z.hcj p)]
    exact congrArg _ (hρ' b a)

  have hB : ∀ b x, (locH Z p).h (g x) (g (baseChange₂ D p b)) = (locH Z p).h x (baseChange₂ D p b) :=
    fun b x => form_ext_left Z p g (baseChange₂ D p b) (g (baseChange₂ D p b)) (fun a => hA a b) x
  have hC : ∀ a y, (locH Z p).h (g (baseChange₂ D p a)) (g y) = (locH Z p).h (baseChange₂ D p a) y := by
    intro a y
    rw [(locH Z p).h_herm (g y) (g (baseChange₂ D p a)), (locH Z p).h_herm y (baseChange₂ D p a), hB]
  refine ⟨g, hext, ?_⟩
  intro x y
  exact form_ext_left Z p g y (g y) (fun a => hC a y) x

end GlobalTheory.LocOver
