import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InputsJumpsAtMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FullConclusionOfInputsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BuiltLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriplesGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameTwistAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFiniteTypesAllStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DutiesOfLarge

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NFacts.AtMemFacts

theorem oneField_of_nAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : Formalism.L2.Host.CharFrame D} {C : NChoice D} {tp : Formalism.L2.Host.TupTied D cf C}
    (a : NAt hL D cf C tp) : GlobalTheory.HeightCounting.SameTw.OneField D C := by
  have key : ∀ X : Σ (D₁ : D7) (c₁ : Formalism.L2.Host.CharFrame D₁) (C₁ : NChoice D₁), Formalism.L2.Host.TupTied D₁ c₁ C₁,
      X = ⟨withLoc a.nt.L, cfL a.nt.L a.nt.cf, chL a.nt.L a.nt.C, tpL a.nt.L a.nt.tp⟩ →
        GlobalTheory.HeightCounting.SameTw.OneField X.1 X.2.2.1 := by
    rintro _ rfl
    exact (GlobalTheory.HeightCounting.SameTw.oneField_withLoc a.nt.L a.nt.C).2 a.nt.Sp.tw_reads
  exact key _ a.nt.pack

theorem facts_atMem : PrN → GlobalTheory.NRows.HypothesesX → SerN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness →
    LocalTateDuality → LocalEulerChar → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => Facts (w.D Z) nch := by
  intro prn prx ser dzw dzs lf ltd lec hL
  have hA := GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.NRows.AtLayer.inputs_jumps_atMem prn prx hL)
    (GlobalTheory.HeightCounting.Up.TripFin.triplesGood prn ser hL)) (GlobalTheory.T.good_finite_types_all prn hL)
  refine EvG.imp hA fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hne hrx cp => ?_
  obtain ⟨⟨⟨I, -, jumps⟩, trip⟩, good⟩ := H kp w Z Wt p0 t nch n xd c hne hrx cp
  obtain ⟨ne⟩ := hne
  have core : Core (w.D Z) := GlobalTheory.T.full_conclusion_of_inputs prn.what₂ prn.hc prn.decay dzw dzs lf ltd lec hL (w.D Z) I jumps
  have large : GlobalTheory.CoefDuty.Large (w.D Z) := ne.large
  exact { core with
    c2 := GlobalTheory.LocCoincide.main hL (w.D Z) I.P.M c.a.nt.toNBuilt I.P.H.hecke
    large := large
    duties := GlobalTheory.CoefDuty.duties_of_large prn.cheb (w.D Z) large core.Conclusion1.1 core.rhoBar
    nct := n.tie
    trip := trip
    same := GlobalTheory.HeightCounting.SameTw.sameTwist_at hL (w.D Z) _ nch _ c.a (oneField_of_nAt c.a)
    good := good }

end GlobalTheory.NFacts.AtMemFacts

end
