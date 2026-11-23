import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocksStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyInnerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalVanishingStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Transp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetry
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker

open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.HCWhittaker

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

section Transport

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem glEquiv_mem_unip (e : α ≃ β) {s : ℕ} (b' : β → Fin s) {u : GL α K}
    (hu : u ∈ unip K (b' ∘ e)) : glEquiv K e u ∈ unip K b' := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  have val : ∀ (g : GL α K) (i j : β), ((glEquiv K e g : GL β K) : Matrix β β K) i j =
      (g : Matrix α α K) (e.symm i) (e.symm j) := fun _ _ _ => rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [val]
    exact h1 _ _ (by simpa using hij)
  · intro i j hij
    rw [← map_inv, val]
    exact h2 _ _ (by simpa using hij)
  · intro i j hij
    rw [val, h3 _ _ (by simpa using hij)]
    simp

theorem isCuspidal_transp (e : α ≃ β) (τ : FDRep ℂ (GL α K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) :
    Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K (transp e τ) := by
  intro s b' hb' hs v hv
  refine h s (b' ∘ e) (hb'.comp e.surjective) hs v fun u hu => ?_
  have := hv _ (glEquiv_mem_unip e b' hu)
  change τ.ρ ((glEquiv K e).symm (glEquiv K e u)) v = v at this
  simpa using this

end Transport

section Matrices

variable {N s : ℕ}

end Matrices

section Term

variable {N s k : ℕ} (b : Fin N → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

end Term

end GlobalTheory.CompanionTheory.TyFin.HCWhittaker
