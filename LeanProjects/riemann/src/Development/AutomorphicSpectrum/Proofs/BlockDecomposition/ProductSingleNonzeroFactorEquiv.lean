import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactorsStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdSingle

theorem prodIrr_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL k) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL k) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  intro k _ _ _ _ h N Y hd i₀ h0
  have hN : (Y i₀).1 = N := by
    rw [← hd]
    exact (Finset.sum_eq_single i₀ (fun i _ hi => h0 i hi) (fun hi => absurd (Finset.mem_univ _) hi)).symm
  subst hN
  refine ⟨(Y i₀).2, Sigma.eta _, ?_⟩
  have hd' : ∑ a : Fin 1, (Y ((fun _ : Fin 1 => i₀) a)).1 = (Y i₀).1 := by simp
  obtain ⟨e₁⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y hd (fun _ : Fin 1 => i₀) (Subsingleton.strictMono _)
    (fun j hj => ⟨0, by
      by_contra hne
      exact hj (h0 j (fun e => hne e.symm))⟩) hd'
  obtain ⟨e₂⟩ := nonempty_equiv_prodIrr_one (Y i₀) hd'
  exact ⟨e₁.trans e₂.symm⟩

end GlobalTheory.CompanionTheory.FineProd.ProdSingle
