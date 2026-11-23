import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses

section
noncomputable section
namespace GlobalTheory.Mem.LiteralAutomorphy
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
structure MemberHypotheses : Prop where
  m1 : GlobalTheory.Published.HarishChandraAnalyticity
  m2 : GlobalTheory.Published.DiscreteSeriesClassification
  m3 : GlobalTheory.Published.CuspRapidDecay
  m4 : GlobalTheory.Published.HarishChandraFinite
  m5 : GlobalTheory.Published.CuspTraceClass
  m6 : GlobalTheory.Published.DixmierMalliavinFactorisation
  m7 : GlobalTheory.Published.FlathFactorisation
  m12 : GlobalTheory.Published.ZelevinskyPolynomialRing
  m13 : GlobalTheory.Published.GeometricLemma
  m14 : GlobalTheory.Published.GreenCuspidal
theorem condition_of_memberHypotheses (c : GlobalTheory.Published.DiscreteSeriesCover) (h1 : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems)
    (h3 : GlobalTheory.Published.HeckeLPartialContinuation) (m : MultL) (r : RowRatW) : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses :=
  ⟨c, h1, h3, m,
    (StepW.and ((StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans m) r).trans
      (StepW.of_all fun _ _ _ _ _ _ _ G Z hX Wt z a b k c d e g u v => ⟨G.1 Z hX Wt z a b c d, G.2 Z hX Wt z a b k c d e g u v⟩)⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
end
