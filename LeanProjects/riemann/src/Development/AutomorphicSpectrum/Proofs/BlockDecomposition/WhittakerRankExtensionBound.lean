import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientRealisedBySubrepsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSubquotientIffWhittakerQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelSupDistributesSubrepsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoGenericSubquotientsImpossibleStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenUniq

theorem nonempty_equiv_of_generic_subquotients (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (N : ℕ) {V W₁ W₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ (GL (Fin N) k) V)
    (π : Representation ℂ (GL (Fin N) k) W₁) (σ : Representation ℂ (GL (Fin N) k) W₂)
    (hρ : IsSmooth ρ)
    (hrank : Module.rank ℂ (TwJacquet ρ (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπρ : IsSubquotient π ρ) (hσρ : IsSubquotient σ ρ)
    (hgπ : IsGenericFor ψ π) (hgσ : IsGenericFor ψ σ) : Nonempty (π.Equiv σ) := by
  obtain ⟨A, B, hBA, ⟨e₁⟩⟩ := GlobalTheory.T.subquotient_realised_by_subreps ρ π hπρ
  obtain ⟨C, D, hDC, ⟨e₂⟩⟩ := GlobalTheory.T.subquotient_realised_by_subreps ρ σ hσρ
  have hiAB : (subQuot A B).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₁ hπ
  have hiCD : (subQuot C D).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₂ hσ
  have hAB := (GlobalTheory.T.generic_subquotient_iff_whittaker_quotient k ψ hψ N ρ hρ A B hBA).1 (hgπ.of_equiv e₁)
  have hCD := (GlobalTheory.T.generic_subquotient_iff_whittaker_quotient k ψ hψ N ρ hρ C D hDC).1 (hgσ.of_equiv e₂)
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_equiv_subQuot_of_not_le_sup ρ (twKer ρ (unipB k (Fin N)) (whitChar ψ N)) hrank
    (GlobalTheory.T.twisted_kernel_sup_distributes_subreps k ψ hψ N ρ hρ) A B C D hBA hDC hiAB hiCD hAB hCD
  exact ⟨(e₁.trans e).trans e₂.symm⟩

end GlobalTheory.CompanionTheory.GenUniq
