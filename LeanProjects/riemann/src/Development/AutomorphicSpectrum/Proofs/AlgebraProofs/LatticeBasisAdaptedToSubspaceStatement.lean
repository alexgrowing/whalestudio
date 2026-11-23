import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspace
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_adapted_to_subspace : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] (i : C.I) (n : ℕ) (b : Module.Basis (Fin n) K V) (L : AddSubgroup V) (W : Submodule K V), IsLatOf C i b L → ∃ (bW : Module.Basis (Fin (Module.finrank K W)) K W) (bQ : Module.Basis (Fin (Module.finrank K (V ⧸ W))) K (V ⧸ W)) (b' : Module.Basis (Fin (Module.finrank K W + Module.finrank K (V ⧸ W))) K V), IsLatOf C i b' L ∧ IsLatOf C i bW (L.comap W.subtype.toAddMonoidHom) ∧ IsLatOf C i bQ (L.map W.mkQ.toAddMonoidHom) ∧ (∀ j, b' (Fin.castAdd _ j) = bW j) ∧ ∀ j, W.mkQ (b' (Fin.natAdd _ j)) = bQ j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted <;> assumption)
