import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexStabilizerEqLocalRelIndex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_stabilizer_eq_local_relIndex : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (J : Subgroup (GAf L n)) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ s.loc n κ ∈ H)) → J.relIndex (GlobalTheory.HeckeScalarSph.locK n s.v) = H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) := by
  first | exact @GlobalTheory.LocRelIndex.main | exact GlobalTheory.LocRelIndex.main | (intros; apply GlobalTheory.LocRelIndex.main <;> assumption)
