import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataKernels
import Formalism.LocalRingCardinality.DataRows
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.LocalRingCardinality.DataCD
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
import Formalism.FrobeniusOrbits.HostOrbitsPlaces
import Formalism.FrobeniusOrbits.HostDiffSupport
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.HostOrbitCountSg
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.CoboundaryTransfers.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import Formalism.FrobeniusOrbits.Statement
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne

namespace Bl.general_b_fact_left_alt

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] {S : Formalism.BasicNotions.HSpace E}
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsLattice.{0, 0, 0} E Λ →
    ∀ (v : S.V),
      Exists.{1} fun (c : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} c 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} c v)) := by
  intro E _ _ _ S Λ hΛ v
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]; trivial
  obtain ⟨y, hy, z, rfl⟩ :=
    (IsLocalization.mem_span_iff (R := NumberField.RingOfIntegers E)
      (M := nonZeroDivisors (NumberField.RingOfIntegers E)) (S := E)).mp hv
  rw [Submodule.span_eq] at hy
  refine ⟨z, nonZeroDivisors.coe_ne_zero z, ?_⟩
  rw [← IsScalarTower.algebraMap_smul E (z : NumberField.RingOfIntegers E), smul_smul,
    IsLocalization.mk'_spec', map_one, one_smul]
  exact hy

end Bl.general_b_fact_left_alt
