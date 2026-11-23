import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

def IrredSt : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (ρ : G →* (H →L[ℂ] H)), IsUnitaryRep ρ → ∀ a Q : H →L[ℂ] H,
  (∀ S : H →L[ℂ] H, (∀ g, S * ρ g = ρ g * S) → S * a = a * S) → (∀ g, Q * ρ g = ρ g * Q) →
  IsCompactOperator (a * Q) → a * Q ≠ 0 → ∃ W, IsIrredSubrep ρ W

def CompSt : Prop := ∀ (D : D7) (V : HSp D) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (w : InfinitePlace D.host.F) (W : Submodule ℂ H),
  IsIrredSubrep (π.comp (embArch D.sp.cm.sig V.gram w)) W →
    ∃ δ : IrrU (GArch D.sp.cm.sig V.gram w), IsIsotypic δ.π (π.comp (embArch D.sp.cm.sig V.gram w))

def CptSt : Prop := GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π →
  mCusp V μ π ≠ 0 → ∀ f ∈ CcGA V, IsCompactOperator (repOp π μ f)

def AdmSt : Prop := ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
  (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π →
  (∀ f ∈ CcGA V, IsCompactOperator (repOp π μ f)) → ∀ hU : IsSubrep π ⊤, IsAdmissible (finPartDSSm M hU)

end MainStatements.Flath2
