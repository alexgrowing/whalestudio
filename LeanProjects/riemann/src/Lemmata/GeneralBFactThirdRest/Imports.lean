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

namespace Bl.general_b_fact_third''''

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] (S : Formalism.BasicNotions.HSpace E)
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsLattice.{0, 0, 0} E Λ →
    ∀ (x : S.V),
      Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} a 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} a x)) := by
  intro E _ _ _ S Λ hL x
  have hx : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hL.2]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • (a • y) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem b hay) (Λ.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨w, hw⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(w.2 : NumberField.RingOfIntegers E) * a, mul_ne_zero (nonZeroDivisors.ne_zero w.2.2) ha, ?_⟩
    have key : ((w.2 : NumberField.RingOfIntegers E) * a) • (c • y) = w.1 • (a • y) := by
      rw [← algebraMap_smul E ((w.2 : NumberField.RingOfIntegers E) * a), ← algebraMap_smul E w.1,
        ← algebraMap_smul E a, smul_smul, smul_smul, ← hw, map_mul]
      congr 1
      ring
    rw [key]
    exact Λ.smul_mem w.1 hay

end Bl.general_b_fact_third''''
