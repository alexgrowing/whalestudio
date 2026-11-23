import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def Res.perC (r : Res l K) : PerC (per l K) where
  C := Bcris l
  K₀ := Wc.K₀ l r.k
  c := cB l
  ι := period_ring_base.ι l
  φ := φB l
  σ g := Formalism.Per6.σB g.1
  q := period_ring_base.qB l
  k := k₀Lift ((cB l).comp r.w) (period_ring_base.isUnit_l l)

def BcrisPeriodFacts : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : Res l K),
  r.perC.Facts ∧ r.perC.ι.range = Bcr l

def CrysPhi : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K),
  Nonempty (CrysCmp Model.Sm r.perC r.iso)

end CrystallineSemistableComparison
