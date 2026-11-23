import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveRootsOfNcardRootSet
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_roots_of_ncard_rootSet' : ∀ {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O), Function.Injective (algebraMap A O) → ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t → P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) → ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  first | exact @GlobalTheory.exists_injective_roots_of_ncard_rootSet | exact GlobalTheory.exists_injective_roots_of_ncard_rootSet | (intros; apply GlobalTheory.exists_injective_roots_of_ncard_rootSet <;> assumption)
