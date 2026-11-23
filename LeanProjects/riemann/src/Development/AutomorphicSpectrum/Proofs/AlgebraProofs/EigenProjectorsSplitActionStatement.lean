import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitAction
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_projectors_split_action : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → ∃ e : S → Module.End K V, (∀ s, IsHom C L L (e s)) ∧ (∀ s x, e s x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)))) ∧ (∀ s, ∀ x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))), e s x = x) ∧ (∀ x, ∑ s, e s x = x) ∧ ∀ s, ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O), (∀ t, ∑ j, c j * χ t (a j) = if t = s then 1 else 0) ∧ e s = ∑ j, algebraMap k K (c j) • ρ (a j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj | exact GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj <;> assumption)
