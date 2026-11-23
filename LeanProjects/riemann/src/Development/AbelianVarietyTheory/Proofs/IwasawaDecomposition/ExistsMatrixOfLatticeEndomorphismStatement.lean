import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixOfLatticeEndomorphism
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_of_lattice_endomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (w : X.Λ →ₗ[𝓞 E] X.Λ), ∃ W : Matrix (Fin r) (Fin r) E, ∀ v : X.Λ, W *ᵥ (v : Fin r → E) = (w v : Fin r → E) := by
  first | exact @GlobalTheory.FlagDomain.lattice_endo_matrix | exact GlobalTheory.FlagDomain.lattice_endo_matrix | (intros; apply GlobalTheory.FlagDomain.lattice_endo_matrix <;> assumption)
