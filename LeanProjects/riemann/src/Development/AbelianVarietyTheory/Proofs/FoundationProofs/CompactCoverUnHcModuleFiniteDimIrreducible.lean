import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDim
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CompactCoverIrr

theorem isKC_of_compact {n : ℕ} (X : Mat n 0) : IsKC X := by
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

theorem map_stable {n : ℕ} (hn : 1 ≤ n) (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (hj : IsHCMod τ M j) (N : Submodule ℂ M.V) [FiniteDimensional ℂ N]
    (hN : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N) (g : T.G) : ∀ x ∈ N.map j, τ.π g x ∈ N.map j := by
  have hg := GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T g (isKC_of_compact _)
  have key : (∀ x ∈ N.map j, τ.π g x ∈ N.map j) ∧ (∀ x ∈ N.map j, τ.π g⁻¹ x ∈ N.map j) := by
    induction hg using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨X, ⟨hX, -⟩, rfl⟩ := hk
      have hf := GlobalTheory.RealPar.flow_mem_map j (M.act X) N (hN X) (fun t => τ.π (T.expt (t • X)))
        (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (hj.2.2 X hX)
      have hinv : (T.expt X)⁻¹ = T.expt ((-1 : ℝ) • X) := by
        have h := T.expt_add X hX 1 (-1)
        rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at h
        exact (eq_inv_of_mul_eq_one_right h.symm).symm
      refine ⟨?_, ?_⟩
      · have := hf 1
        rwa [one_smul] at this
      · rw [hinv]
        exact hf (-1)
    | one => refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simpa using hx
    | mul a b _ _ ha hb =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [map_mul]
        exact ha.1 _ (hb.1 x hx)
      · rw [mul_inv_rev, map_mul]
        exact hb.2 _ (ha.2 x hx)
    | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩
  exact key.1

theorem eq_bot_or_top {n : ℕ} (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (hτ : IrrU τ) (hj : Function.Injective j) (N : Submodule ℂ M.V) [FiniteDimensional ℂ N]
    (hN : ∀ g, ∀ x ∈ N.map j, τ.π g x ∈ N.map j) : N = ⊥ ∨ (N = ⊤ ∧ N.map j = ⊤) := by
  rcases hτ.2 (N.map j) (Submodule.closed_of_finiteDimensional _) hN with h | h
  · left
    apply Submodule.map_injective_of_injective hj
    rw [h, Submodule.map_bot]
  · right
    refine ⟨?_, h⟩
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, hwv⟩ : j v ∈ N.map j := h ▸ Submodule.mem_top
    exact hj hwv ▸ hw

theorem hcMod_finite_irr : ∀ (n : ℕ), 1 ≤ n → ∀ (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H), IrrU τ → IsHCMod τ M j → Nontrivial M.V → FiniteDimensional ℂ M.V ∧ IrrGK M ∧ (∀ h v, ∃ v', j v' = τ.π h (j v)) ∧ ∀ N : Submodule ℂ M.V, (∀ h, ∀ v ∈ N, ∀ v', j v' = τ.π h (j v) → v' ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n hn T τ M j hτ hj hM
  obtain ⟨v, hv⟩ := exists_ne (0 : M.V)
  obtain ⟨W, hWf, hvW, hWs⟩ := M.kfin v
  have hW := (eq_bot_or_top T τ M j hτ hj.1 W
    (map_stable hn T τ M j hj W fun Z => hWs Z (isKC_of_compact Z))).resolve_left
    (fun h => hv (by rw [h] at hvW; exact hvW))
  have hfin : FiniteDimensional ℂ M.V := by
    rw [hW.1] at hWf
    exact Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule ℂ M.V) ≃ₗ[ℂ] M.V)
  have hsurj : ∀ x, ∃ v', j v' = x := fun x => by
    obtain ⟨w, -, hw⟩ : x ∈ W.map j := hW.2 ▸ Submodule.mem_top
    exact ⟨w, hw⟩
  refine ⟨hfin, ⟨hM, fun N hN => ?_⟩, fun h v => hsurj _, fun N hN => ?_⟩
  · exact (eq_bot_or_top T τ M j hτ hj.1 N (map_stable hn T τ M j hj N hN)).imp_right And.left
  · refine (eq_bot_or_top T τ M j hτ hj.1 N ?_).imp_right And.left
    rintro g _ ⟨w, hw, rfl⟩
    obtain ⟨v', hv'⟩ := hsurj (τ.π g (j w))
    exact ⟨v', hN g w hw v' hv', hv'⟩

end GlobalTheory.CompactCoverIrr
