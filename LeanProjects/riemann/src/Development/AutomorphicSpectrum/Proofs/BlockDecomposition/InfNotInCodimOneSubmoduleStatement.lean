import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmodule
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_not_in_codim_one_submodule : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (T : Submodule ℂ V), Module.rank ℂ (V ⧸ T) ≤ 1 → ∀ A C : Subrepresentation ρ, (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T → ¬ A.toSubmodule ≤ T → ¬ C.toSubmodule ≤ T → ¬ (A ⊓ C).toSubmodule ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | exact GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | (intros; apply GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet <;> assumption)
