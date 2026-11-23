import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPlace

theorem under_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (h : Formalism.L2.NTheta.IsIdemAt q.e PP) :
    HeightOneSpectrum.under (𝓞 D.host.F) PP = q.v := by
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h
  obtain ⟨ε, hε, h3⟩ := q.above
  have h2 := q.split.2.1
  have h4 := GlobalTheory.IdemSupport.ev_mul (Φ := (GlobalTheory.StdFrames.toAd D).comp (toEAf D)) q.e (cA D q.e) PP
  rw [h2, GlobalTheory.IdemSupport.ev_zero, hd.2.1, one_mul, eq_comm] at h4
  by_contra hv
  have := (GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 PP hv
  rw [← h3, GlobalTheory.IdemSupport.ev_add, h4, hd.2.1, add_zero] at this
  exact one_ne_zero this

theorem v_eq_of_isIdemAt : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (PP : Formalism.L2.DIV.Pl D.host.E),
    Formalism.L2.NTheta.IsIdemAt q.e PP → Formalism.L2.NTheta.IsIdemAt q'.e PP → q.v = q'.v :=
  fun _ _ _ _ _ _ _ _ _ _ _ q q' PP h h' => (under_eq q PP h).symm.trans (under_eq q' PP h')

end GlobalTheory.FinPl.SplitPlace
