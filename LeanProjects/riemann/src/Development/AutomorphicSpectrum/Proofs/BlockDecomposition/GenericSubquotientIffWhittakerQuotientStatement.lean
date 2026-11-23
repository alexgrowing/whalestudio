import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSubquotientIffWhittakerQuotient
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_subquotient_iff_whittaker_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ A B : Subrepresentation ρ, B ≤ A → (IsGenericFor ψ (subQuot A B) ↔ ¬ A.toSubmodule ≤ B.toSubmodule ⊔ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff | exact GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff | (intros; apply GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff <;> assumption)
