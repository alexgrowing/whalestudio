import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem pgFrame_at_record : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → Formalism.L2.SG.RowsConc.TFrameAt D ∧ UnitaryVolumeMass.cTvA D ∧ UnitaryVolumeMass.cTvD D 1 ∧ ∀ w τ, (D.R.k : ℝ) ^ (3 * D.R.rS) ≤ gg D ^ (-(D.R.m : ℝ)) * Tcrit D w τ := by
  intro hSM hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT h h40 hCu hk hR
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hyp : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT := ⟨h.2.1, h.1, h.2.2⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hg : LocalBesselAndTopKernel.MidVolumeChain D large₂ (1 / 3) 0 :=
    Formalism.L2.SG.Pf.SzHypFam.midVolumeChain_of_standingHypotheses hT h.1 (by nlinarith) (by norm_num) le_rfl
  have hD : UnitaryVolumeMass.cTvD D 1 :=
    Formalism.MainNotions.BridgeLemma.critical_level_lower_bound (C3' := 1) h40 (by norm_num) le_rfl hyp hg
  have hA : UnitaryVolumeMass.cTvA D :=
    Formalism.MainNotions.BridgeLemma.degree_ratio_formula_statement D large₂ C0 C' Cl Cg cb Cu cT CT
      (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hSM D) (Formalism.MainNotions.BridgeLemma.mass_two_bound_single_holds D) hR hyp
  have F := Formalism.MainNotions.BridgeLemma.tfFacts_of h
  have hm : 2 * (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; norm_num; exact_mod_cast this
  exact ⟨fun w => F.tframe (by linarith) hm hCu hA hD hk w, hA, hD,
    fun w τ => F.tcritLow (by linarith) hm hCu hD w τ⟩

end GlobalTheory
