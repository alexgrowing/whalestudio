import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RkSubSuccLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainLengthBoundOfSupInfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRankSubmoduleChainBoundedStatement

noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.ThetaGLSub GlobalTheory.ThetaGLRank

namespace GlobalTheory.ThetaGLRank

theorem boundedChains_thetaGL : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} →
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i)) → r ≤ L := by
  intro P k _ _ _ _ n m χ hχ
  have key : ∀ d : ℕ, ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, IsSub χ (N i) ∧ N i ≤ aug m χ ⊔ rkSub k n m (n + 1 - d)) → r ≤ L := by
    intro d
    induction d with
    | zero =>
      refine ⟨1, fun r N hN hQ => ?_⟩
      by_contra h
      push_neg at h
      have e : ∀ i, N i = aug m χ := fun i =>
        le_antisymm (by simpa [rkSub_succ_n] using (hQ i).2) (hQ i).1.1
      have hlt : (⟨0, by omega⟩ : Fin r) < ⟨1, h⟩ := by simp [Fin.lt_def]
      exact (hN hlt).ne (by rw [e, e])
    | succ d ih =>
      obtain ⟨L1, h1⟩ := ih
      by_cases hd : d ≤ n
      · obtain ⟨L2, h2⟩ := GlobalTheory.T.theta_rank_submodule_chain_bounded P k n m χ hχ (n - d)
        have e1 : n + 1 - d = n - d + 1 := by omega
        have e2 : n + 1 - (d + 1) = n - d := by omega
        refine ⟨L1 + L2, GlobalTheory.T.chain_length_bound_of_sup_inf (aug m χ ⊔ rkSub k n m (n + 1 - d))
          (fun x => IsSub χ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n + 1 - (d + 1)))
          (fun x => IsSub χ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n + 1 - d))
          (fun x => IsSub χ x ∧ aug m χ ⊔ rkSub k n m (n - d + 1) ≤ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n - d))
          L1 L2 ?_ ?_ h1 (fun r N hN hQ => h2 r N hN hQ)⟩
        · intro x hx
          exact ⟨GlobalTheory.ThetaGLRank.IsSub.inf hx.1 (isSub_aug_sup χ _), inf_le_right⟩
        · intro x hx
          refine ⟨GlobalTheory.ThetaGLSub.IsSub.sup hx.1 (isSub_aug_sup χ _), ?_, ?_⟩
          · rw [← e1]; exact le_sup_right
          · refine sup_le (e2 ▸ hx.2) ?_
            rw [e1]
            exact sup_le_sup_left (rkSub_succ_le _) _
      · refine ⟨L1, fun r N hN hQ => h1 r N hN fun i => ⟨(hQ i).1, ?_⟩⟩
        have : n + 1 - (d + 1) = n + 1 - d := by omega
        rw [← this]; exact (hQ i).2
  obtain ⟨L, hL⟩ := key (n + 1)
  refine ⟨L, fun r N hN hQ => hL r N hN fun i => ⟨hQ i, ?_⟩⟩
  rw [Nat.sub_self, rkSub_zero]
  exact le_sup_of_le_right (hQ i).2.1

end GlobalTheory.ThetaGLRank
