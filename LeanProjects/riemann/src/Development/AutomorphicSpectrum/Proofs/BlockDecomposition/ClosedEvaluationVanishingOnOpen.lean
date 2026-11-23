import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Off

variable {k : Type} [Field k]

theorem sEmb_row (n : ℕ) (m : Mir k n) (j : Fin (n + 1 + 1)) :
    (((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
      (Fin.castSucc (Fin.last n)) j = (1 : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hs : ((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmb k (n + 1) (m : GL (Fin (n + 1)) k) := rfl
  have hm : Matrix.vecMul (GlobalTheory.BZMir.eLast k n) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.eLast k n := m.2
  rw [GlobalTheory.BZMir.vecMul_eLast] at hm
  rw [hs]
  show GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (Fin.castSucc (Fin.last n)) j = _
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne]
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
    rw [hm]
    by_cases hj : j' = Fin.last n
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · rw [Matrix.one_apply_ne (fun e => hj (Fin.castSucc_injective _ e).symm)]
      simp [GlobalTheory.BZMir.eLast, Pi.single_apply, hj]

theorem dEmb_mul_sEmb_mem_Cl (i t : ℕ) (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) :
    dEmb k i t d * sEmb k _ m ∈ Cl k i t := by
  simp only [Cl, Set.mem_ofPred_eq]
  intro c
  rw [_root_.mul_inv_rev, ← map_inv, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  simp_rw [sEmb_row]
  rw [← Matrix.mul_apply, Matrix.one_mul]
  show ((1 : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) -
      GlobalTheory.BZMir.colMat k (i + 1 + (t + 1)) (Fin.append 0 d)) _ _ = 0
  rw [Matrix.sub_apply]
  have hRC : (Fin.last (i + 1 + t)).castSucc ≠ (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  have hCL : (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) ≠ Fin.last (i + 1 + (t + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  rw [Matrix.one_apply_ne hRC]
  simp [GlobalTheory.BZMir.colMat, hCL]

end GlobalTheory.CompanionTheory.BZPhiPG.Off

open GlobalTheory.CompanionTheory.BZPhiPG.Off in

theorem GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
    eC ψ f = 0 := by
  intro k _ _ _ _ i t ψ τ σ hτ hσ f hf
  funext m
  have hz : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * sEmb k (i + 1 + t) m) = 0 :=
    fun d => hf _ (dEmb_mul_sEmb_mem_Cl i t d m)
  have hint : intC ψ f (sEmb k (i + 1 + t) m) = 0 := by
    unfold intC
    simp only [hz, smul_zero]
    unfold GlobalTheory.CompanionTheory.Rodier.smInt
    apply finsum_eq_zero_of_forall_eq_zero
    intro w
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have hpre : ((fun _ => (0 : TensorProduct ℂ τ.V σ.V)) : (Fin (t + 1) → k) → TensorProduct ℂ τ.V σ.V) ⁻¹' {w} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h0 => hw h0.symm
      rw [hpre, MeasureTheory.measure_empty]
      simp
  simp only [eC, hint, map_zero, smul_zero, Pi.zero_apply]

end
