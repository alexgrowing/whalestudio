import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOPerm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

theorem exists_rowMatchS : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b →
    ∃ G' : GlobalTheory.Grid.GridPre R, G'.Is ∧ GlobalTheory.RowLift.RowMatchS ch G' := by
  intro hP D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hb CF hs
  have hsc : ch.sc.cGap = 1 := by rw [hs]
  obtain ⟨G, hG, hsp, harr⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
    hP.harishChandraModules hS.host hS.size hS.core hsc ch.W hb.weil
  have hfr : ∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
    rintro (_ | i) hi
    · obtain ⟨c, h⟩ := hS.core.lev.βY 0 (by have := D.R.two_le_m; omega)
      exact h.1
    · obtain ⟨c, h⟩ := (hG.spaces.vert i 0 hi (Nat.zero_le _)).frame
      exact h.1
  obtain ⟨m00, mV, hm, hν, hfd⟩ := GlobalTheory.ColMeas.measCol_of_choice ch G hG.meas hsp hfr hb.vol
  refine ⟨GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX, ⟨GlobalTheory.GridJoin.isSpaces_withMeas hG.spaces,
    GlobalTheory.GridJoin.isChars_withMeas hG.chars, GlobalTheory.GridJoin.isArrows_withMeas hG.arrows, hm,
    GlobalTheory.GridJoin.isData_withMeas hG.data⟩, ⟨fun i hi => (hsp.vert i 0 hi (Nat.zero_le _)).sp, hν, hfd,
    GlobalTheory.RowKer.kernel_row ch (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _
      (hS.core.lev.βY 0 (by have := D.R.two_le_m; omega))) hb.weil G hG ⟨hsp, harr⟩⟩⟩

end GlobalTheory.RowLift

end
