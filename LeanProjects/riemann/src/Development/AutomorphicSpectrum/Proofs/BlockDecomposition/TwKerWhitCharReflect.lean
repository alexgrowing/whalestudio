import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupOfFinset

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PRep.WhitExact

theorem twKer_whitChar_reflect : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth π → IsSmooth σ → ∀ f : V →ₗ[ℂ] W, Function.Injective f → (∀ g v, f (π g v) = σ g (f v)) → ∀ v : V, f v ∈ twKer σ (unipB k (Fin N)) (whitChar ψ N) → v ∈ twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ N V W _ _ _ _ π σ hπ hσ f hf hfg v hv
  exact GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect π σ hπ hσ _ _
    (GlobalTheory.Whittaker.isSmoothChar_whitChar hψ)
    (fun s hs => GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N s hs) f hf hfg v hv

end GlobalTheory.CompanionTheory.PRep.WhitExact
