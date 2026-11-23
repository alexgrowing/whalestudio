import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnipotentSubgroupFiniteGeneration
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_unipotent_subgroup_finite_generation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (Q : Subgroup (GL (Fin N) k)), Q ≤ unipB k (Fin N) → (∀ s : Finset (GL (Fin N) k), (↑s : Set (GL (Fin N) k)) ⊆ Q → ∃ L : Subgroup (GL (Fin N) k), L ≤ Q ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k))) → ∀ θ : Q →* ℂˣ, (∀ (q : Q) (hq : (q : GL (Fin N) k) ∈ unipB k (Fin N)), θ q = whitChar ψ N ⟨q, hq⟩) → ∀ f ∈ openFns d hd ρ, f ∈ twKer (parInd (stdBlocks d hd) ρ) Q θ → f ∈ Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ, x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g} := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer | exact GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer <;> assumption)
