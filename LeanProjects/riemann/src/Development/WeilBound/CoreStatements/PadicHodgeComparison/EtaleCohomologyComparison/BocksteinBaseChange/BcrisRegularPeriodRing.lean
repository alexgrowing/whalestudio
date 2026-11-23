import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.SemistableModelSemistable
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ThetaSetupAlgebraMaps

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

def per (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Per l K where
  A := ACris.ACris ℂ_[l] l
  B := BdR l
  i := iC l
  t := tA l
  z := (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)).comp (IsPerfectoidField.padicIntToWitt l)
  φ := ACris.phi ℂ_[l] l
  σA g := ACris.galCris (IntermediateField.fixingSubgroupEquiv K g)
  σ g := (σD g.1 : BdR l ≃+* BdR l).toRingHom
  q := qQ l
  o := oK
  P := (algebraMap (BdRp l) (BdR l)).range

def PeriodRingFacts : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (per l K).Facts

def BcrisRegularPeriodRing : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  (per l K).Reg (Bcr l)

def BstRegularPeriodRing : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  (per l K).Reg (Bst l)

end CrystallineSemistableComparison
