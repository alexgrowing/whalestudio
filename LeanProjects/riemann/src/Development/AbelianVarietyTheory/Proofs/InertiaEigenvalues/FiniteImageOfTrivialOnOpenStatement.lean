import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteImageOfTrivialOnOpen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_of_trivial_on_inf_isOpen : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (Q : Type) [Group Q] (ρ : ↥(GK K) →* Q) (J H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set ↥(GK K))).Finite := by
  first | exact @GlobalTheory.GK.finite_image_of_trivial_on_open | exact GlobalTheory.GK.finite_image_of_trivial_on_open | (intros; apply GlobalTheory.GK.finite_image_of_trivial_on_open <;> assumption)
