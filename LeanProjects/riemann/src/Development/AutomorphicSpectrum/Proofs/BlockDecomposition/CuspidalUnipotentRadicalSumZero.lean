import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspSum

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem blk_unip (b : ι → Fin s) (c : Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    Formalism.IrreducibleCountingLemmas.TYPES.blk K b c (g : Matrix ι ι K) = 1 := by
  ext ⟨i, hi⟩ ⟨l, hl⟩
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply, Subtype.mk.injEq]
  exact hg.2 i l (hi.trans hl.symm)

omit [Fintype K] [DecidableEq K] [Fintype ι] in

theorem entry_of_blk (b : ι → Fin s) {M : Matrix ι ι K}
    (h : ∀ c, Formalism.IrreducibleCountingLemmas.TYPES.blk K b c M = 1) (i j : ι) (hij : b i = b j) :
    M i j = if i = j then 1 else 0 := by
  have := congrFun (congrFun (h (b j)) ⟨i, hij⟩) ⟨j, rfl⟩
  simpa only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply,
    Subtype.mk.injEq] using this

theorem unip_mul_mem (b : ι → Fin s) {g h : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) (hh : h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    g * h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨mul_mem hg.1 hh.1, entry_of_blk b fun c => ?_⟩
  rw [Units.val_mul, Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.1 hh.1.1, blk_unip b c hg, blk_unip b c hh,
    one_mul]

theorem unip_inv_mem (b : ι → Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) : g⁻¹ ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨inv_mem hg.1, entry_of_blk b fun c => ?_⟩
  have h := Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.2 hg.1.1
  rw [Units.inv_mul, blk_unip b c hg, mul_one] at h
  rw [← h]
  exact Matrix.submatrix_one _ Subtype.val_injective

open Classical in

theorem sum_rho_unip (τ : FDRep ℂ (GL ι K)) (hc : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ)
    (b : ι → Fin s) (hb : Function.Surjective b) (hs : 2 ≤ s) :
    (∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0) = 0 := by
  set P : Module.End ℂ τ := ∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0
    with hP
  have hfix : ∀ a ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b, τ.ρ a * P = P := by
    intro a ha
    rw [hP, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft a)
      (fun v : GL ι K => if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hiff : a * v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b ↔ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
      refine ⟨fun h => ?_, unip_mul_mem b ha⟩
      simpa using unip_mul_mem b (unip_inv_mem b ha) h
    simp only [Equiv.coe_mulLeft, hiff]
    split_ifs
    · rw [map_mul]
    · rw [mul_zero]
  refine LinearMap.ext fun w => ?_
  exact hc s b hb hs (P w) fun a ha => LinearMap.congr_fun (hfix a ha) w

theorem twoBlock_surjective {d j : ℕ} (hj : 1 ≤ j) (hjd : j < d) :
    Function.Surjective (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) := by
  intro c
  fin_cases c
  · exact ⟨⟨0, by omega⟩, by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]; omega⟩
  · exact ⟨⟨j, hjd⟩, by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]⟩

theorem sum_character_translate :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ j → j < d → IsCuspidal K τ → ∀ u : GL (Fin d) K,
    (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.character (u * v) else 0) = 0 := by
  intro K _ _ _ d j τ hj hjd hc u
  classical
  have h0 := sum_rho_unip τ hc (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) (twoBlock_surjective hj hjd) le_rfl
  have h1 : LinearMap.trace ℂ τ (τ.ρ u * ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.ρ v else 0) = 0 := by
    rw [h0, mul_zero, map_zero]
  rw [Finset.mul_sum, map_sum] at h1
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) h1
  split_ifs
  · rw [FDRep.character, map_mul]
  · rw [mul_zero, map_zero]

end GlobalTheory.CompanionTheory.TyFin.CuspSum
