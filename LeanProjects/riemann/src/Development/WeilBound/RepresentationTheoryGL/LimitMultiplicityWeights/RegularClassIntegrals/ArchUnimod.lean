import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel

def CuspAny : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), NoFixed T →
    ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) →
    ∀ ff, IsTestFin T U μf ff → ∀ fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ,
      (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → MainStatements.RegularCuspidalTrace.IsCuspFn (tensor D.sp.cm.sig V.gram fa ff)

def ArchGroup : Prop :=
  ∀ (D : D7) (V : HSp D) (w : InfinitePlace D.host.F) (τ : EmbOver D.host.E w),
    IsUGroup (archMat D.sp.cm.sig V.gram τ) (V.gram.map τ.1)

def ArchUnimod : Prop :=
  ∀ (D : D7) (V : HSp D) (w : InfinitePlace D.host.F) (μ : Measure (GArch D.sp.cm.sig V.gram w)),
    μ.IsHaarMeasure → μ.IsMulRightInvariant

def ArchZero : Prop :=
  ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff →
    (∀ fa' : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ, (∀ w, fa' w ∈ CcArch D.sp.cm.sig V.gram w) →
      MainStatements.RegularCuspidalTrace.IsCuspFn (tensor D.sp.cm.sig V.gram fa' ff)) →
    ∀ γ : GF V, IsRegSS γ.1.1 → ∀ (w : InfinitePlace D.host.F) (μw : Measure (GArch D.sp.cm.sig V.gram w))
      [μw.IsHaarMeasure] (ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ)))) [ds.IsHaarMeasure]
      [ds.IsMulRightInvariant], HasOrbInt μw (projArch D.sp.cm.sig V.gram w (rat V γ)) ds (fa w) 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (rat V γ)

end MainStatements.WeightKernel

end
