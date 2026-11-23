import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEOfIsBlockSum

noncomputable section

namespace GlobalTheory.AmbBlockDecomp

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem sum_ind_block (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : ℤ) else 0)) =
      if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.toNat, (Int.toNat_of_nonneg h.1).symm⟩
    rw [Finset.sum_eq_single (n + 1)]
    · simp
    · intro b _ hb
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  intro D i r ρ π hD _ _ _ w hw C τ
  have hB : GlobalTheory.PtCore.BlockE D i r ρ π :=
    GlobalTheory.BlockEnl.blockE_of_isBlockSum D i r ρ π (by
      obtain ⟨e, he⟩ := hD
      exact ⟨e, fun g u => he g u⟩)
  obtain ⟨h1, h2⟩ := hB w hw C.LL C.le τ
  have hl : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)),
      TruncatedSeriesCountingIdentities.locC C M = GlobalTheory.PtCore.locE D i w hw C.LL C.le M := fun _ => rfl
  simp only [hl]
  refine ⟨fun a => ?_, fun c hc a => h2 c hc a⟩
  rw [h1 a]
  congr 1
  rw [Finset.sum_congr rfl (fun c hc => h2 c hc a)]
  exact (sum_ind_block D.R.t a).symm

end GlobalTheory.AmbBlockDecomp
