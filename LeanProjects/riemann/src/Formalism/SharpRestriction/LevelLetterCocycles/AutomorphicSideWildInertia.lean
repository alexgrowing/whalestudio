import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualConditionOnLinkedSides
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section

namespace Formalism.MainNotions.AutomorphicSideWildInertia

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def ResidualIrreducibleGood (D : D7) : Prop := ResidualIrreducibleRankR D

def AdmRhoBar (D : D7) : Prop :=
  SumRepresentations.tie0 D ∧ SumRepresentations.adm2 D ∧ SumRepresentations.ArchimedeanSignatureMatching D ∧ SumRepresentations.adm5 D ∧ SumRepresentations.Conclusion41 D ∧ SumRepresentations.Conclusion42 D ∧ ArithmeticCylinders.adm3 D ∧ ArithmeticCylinders.ArchimedeanSignatureMatching D

def ResidualIrreducibleTheorem (D : D7) : Prop := AdmRhoBar D → ResidualIrreducibleGood D

def WildInertiaTrivial (D : D7) : Prop := GlobalDatumLocalisationCondition D

def AdmWild (D : D7) : Prop := SigTie D ∧ SumRepresentations.tie0 D ∧ SumRepresentations.adm2 D ∧ SumRepresentations.ArchimedeanSignatureMatching D ∧ SumRepresentations.Conclusion41 D

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal in

def WildGap (D : D7) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s : D.ntw.Sig i, ¬ SideLoc D i (D.ntw.side i s) → ∀ k, D.host.g k ≠ D.ntw.l i →
    ∀ v ∈ placesOver D.host.E (D.host.g k), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ : G D.host.E D.nd.Om, Formalism.MainNotions.BlochKatoReduction.IsWild A σ → Formalism.MainNotions.BlochKatoReduction.Gen.rbar D.ntw i s σ = 1

def WildInertiaTheorem (D : D7) : Prop := AdmWild D → WildGap D → WildInertiaTrivial D

def AutomorphicSideConclusion (D : D7) (bkP : BlochKatoReduction.BK D) : Prop := BlochKatoReduction.adm1 bkP

def AutomorphicSideHypotheses (D : D7) : Prop :=
  SigTie D ∧ SumRepresentations.tie0 D ∧ SumRepresentations.adm2 D ∧ SumRepresentations.ArchimedeanSignatureMatching D ∧ SumRepresentations.Conclusion41 D ∧ SumRepresentations.CuspidalGaloisUnramified D ∧ SumRepresentations.Conclusion42 D

def AutomorphicSideOpenCase (D : D7) (bkP : BlochKatoReduction.BK D) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s : D.ntw.Sig i, ¬ SideLoc D i (D.ntw.side i s) → BlochKatoReduction.Gen.IsotypicValuationAtRing bkP i s

def AutomorphicSideTheorem (D : D7) (bkP : BlochKatoReduction.BK D) : Prop := AutomorphicSideHypotheses D → AutomorphicSideOpenCase D bkP → AutomorphicSideConclusion D bkP

end Formalism.MainNotions.AutomorphicSideWildInertia
