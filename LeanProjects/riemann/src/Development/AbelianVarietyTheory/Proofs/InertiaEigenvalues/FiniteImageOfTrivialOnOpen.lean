import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexOfIsOpenAbsGaloisFinExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteOfTrivialOnInfFiniteIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem GK.finite_image_of_trivial_on_open :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (Q : Type) [Group Q] (ρ : ↥(GK K) →* Q)
      (J H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → (∀ g ∈ J, g ∈ H → ρ g = 1) →
      (ρ '' (J : Set ↥(GK K))).Finite := by
  intro l _ K Q _ ρ J H hH hρ
  haveI := GlobalTheory.T.finiteIndex_of_isOpen_absGalois_finExt l K H hH
  exact GlobalTheory.T.finite_image_of_trivial_on_inf_finiteIndex _ Q ρ J H inferInstance hρ

end GlobalTheory
