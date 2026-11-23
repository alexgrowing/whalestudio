import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPrimeComponent_finset_prod : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ (∅ : Finset ℕ)) y = 1 ∧ ∀ (q : ℕ) (s : Finset ℕ), q ∉ s → GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ insert q s) y = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y * GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ s) y := by
  first | exact @GlobalTheory.NormSum.VacInt.PartFin.part_finset | exact GlobalTheory.NormSum.VacInt.PartFin.part_finset | (intros; apply GlobalTheory.NormSum.VacInt.PartFin.part_finset <;> assumption)
