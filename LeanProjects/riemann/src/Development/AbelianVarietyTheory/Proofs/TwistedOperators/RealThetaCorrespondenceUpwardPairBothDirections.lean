import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.EvenOnto

theorem upPair_down {D : D7} {X : ProvA} (h : GlobalTheory.ArchRec.Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) (τ : D.what₂.Tau) (V W : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ForAllAt τ V W aS aT S S' fun MS MT A B pt =>
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.LiftLaw MT τ B pt MS A ∧ ∀ ip, GlobalTheory.ArchRec.IsIp V W ip → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaLaw MT τ B pt MS A ip := by
  obtain ⟨al, be, ga, de, hd, -, rfl, rfl⟩ := hp
  intro ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf
  obtain ⟨hm, e, u, hk⟩ := GlobalTheory.ArchRec.tie_small h hd.1 MS τ true false p1
  obtain ⟨e', u', hk'⟩ := GlobalTheory.ArchRec.tie_large h hd.1 MT τ false true p2
  obtain ⟨κ, hR⟩ := GlobalTheory.ArchRec.exists_real hω hS hT (GlobalTheory.ArchRec.isFrameOf_model MS τ) (GlobalTheory.ArchRec.isFrameOf_model MT τ) hf
    hk.ord.1 hk'.ord.1
  exact GlobalTheory.ArchRec.lift_down h h1 h3 hd hm hk hk' hR

theorem pairPar_of_upPair {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) :
    GlobalTheory.PairLift.PairPar S S' aS aT ∧ GlobalTheory.PairLift.PairPar S' S aT aS := by
  obtain ⟨al, be, ga, de, hd, hfar, rfl, rfl⟩ := hp
  have hT : GlobalTheory.PairLift.ThetaPar t (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) (GlobalTheory.Chain.signed (al ++ block t ++ de) (ga ++ be) aS) aT aS :=
    ⟨al, be, ga, de, rfl, Or.inl ⟨hd, rfl⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + aT := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨⟨t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩, ⟨t, _, _, rfl, rfl, Or.inr hT⟩⟩

theorem upPair_arch : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (S S' : SPar) (aS aT : ℚ),
    UpPair t S S' aS aT → (∀ (τ : D.what₂.Tau) (V W : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ToSource τ V W aS aT S S' ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaSource τ V W aS aT S S') ∧ ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X →
      Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → GlobalTheory.PairLift.RulePar X S S' aS aT ∧ GlobalTheory.PairLift.RulePar X S' S aT aS := by
  intro hDS hHC D t S S' aS aT hp
  refine ⟨fun τ V W => ?_, fun X h3 h4 h5 => ?_⟩
  · obtain ⟨X, hX, h1, -, h3, -, -⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
    have h : GlobalTheory.ArchRec.Good D X :=
      ⟨hX, GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX, hHC.admQ5_of_harishChandraModules X, GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D⟩
    have down := upPair_down h h1 h3 hp τ V W
    exact ⟨fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).1,
      fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf μ 𝓕 m1 m2 =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).2 _ ⟨μ, 𝓕, m1, m2, rfl⟩⟩
  · obtain ⟨q1, q2⟩ := pairPar_of_upPair hp
    exact ⟨GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q1, GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q2⟩

end GlobalTheory.EvenOnto

end
