import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NeatTies
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FinXP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_Gflag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} (n m : ℕ)
    (F : FlagG S r (n : E)) (F' : FlagG S r (m : E)) : star (Gflag F F') = Gflag F F' := by
  unfold Gflag
  simp only [star_sub, star_mul', star_star, star_natCast]
  ring

theorem greal_holds {D : D7} {X : HidaSetting D} (Y : Full X) : ∀ u u' (t : RT Y u u'), t.G ∈ D.host.F := by
  intro u u' t
  rw [← Formalism.BasicNotions.Examples₂.conj_eq_self_iff D.host, ← Formalism.BasicNotions.Examples₂.star_eq_conj D.host]
  exact star_Gflag _ _ _ _

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem phLoc_int_of_gap {D : D7} (X : HidaSetting D) (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (v : InfinitePlace X.B.I.F) (d : ℝ) :
    Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) d) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
    (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X Formalism.L2.SG.Closed.CoefWeightedLoc_holds hg) v
  have hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
    h.mono (continuous_star.comp_aestronglyMeasurable h.1) (ae_of_all _ fun g => le_of_eq (norm_star _))
  exact hs.const_mul (d : ℂ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem finX_holds (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim) (hFL : Formalism.L2.SG.Pf.FinLeviC)
    (hK : IotaKer) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC := by
  intro D T hg
  obtain ⟨hWD, hph⟩ := hWu D hg T.X
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties T.X
  have hfold : ∀ u, Formalism.L2.SG.WuDecay.FoldOK T.X u T.Y.hK := fun u =>
    Formalism.L2.SG.Closed.FoldOKC_holds hFL D T.X T.Y u hK2 hWD
  exact finX_of_neat T.Y (fun u => Formalism.L2.SG.Pf.neatKu_full D T.X T.Y u)
    (fun u => Formalism.L2.SG.Closed.InHHC_holds D T.X T.Y u hph (hfold u))
    (Formalism.L2.SG.Pf.RowDictPf.finiteDimensional_HHX_of_hypotheses T.X hRF Formalism.L2.SG.Pf.RowDictPf.schur_orthogonality_discrete_series
      (fun v => phLoc_int_of_gap T.X hg v _))
    (fun u u' t => fibFin_holds D T.X T.Y u u' t)
    (fun u u' s₁ s₂ s₁' s₂' h1 h2 h3 h4 => pairIndep_of hK D T.X T.Y u u' s₁ s₂ s₁' s₂' h1 h2 h3 h4)
    (greal_holds T.Y) Formalism.L2.SG.Closed.VolPosC_holds

end Formalism.L2.SG.Pf.FinXP

end
