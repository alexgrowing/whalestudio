import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusWeightOfPolyRepGLComplexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusWeightMaximizingWeightedSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransvectionWeightVecExpansionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitriangularInductionTransvectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GLUpperTriangularEqDiagonalMulUnitriangularStatement

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem exists_isBEig_of_isPolyRep :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
      IsPolyRep Φ → ∃ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam := by
  intro n ι _ _ _ Φ hΦ
  obtain ⟨μ₀, hμ₀⟩ := GlobalTheory.T.exists_torusWeight_of_polyRep_GL_complex n ι Φ hΦ
  obtain ⟨μ, ⟨v, hv0, hvw⟩, hmax⟩ := GlobalTheory.T.exists_torusWeight_maximizing_weighted_sum n ι Φ μ₀ hμ₀
  refine ⟨v, μ, hv0, fun B hB => ?_⟩
  have hU : ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → Φ U *ᵥ v = v := by
    refine GlobalTheory.T.unitriangular_induction_on_transvections n (fun U => Φ U *ᵥ v = v) (by simp [hΦ.one]) (fun A C hA hC => ?_) ?_
    · show Φ (A * C) *ᵥ v = v
      rw [hΦ.mul, ← mulVec_mulVec, hC, hA]
    · intro i j hij s C hC
      show Φ C *ᵥ v = v
      obtain ⟨K, w, hw0, hww, hsum⟩ := GlobalTheory.T.exists_transvection_weightVec_expansion n ι Φ hΦ i j (ne_of_lt hij) μ v hvw
      have hz : ∀ k, k ≠ 0 → w k = 0 := by
        intro k hk
        by_contra hne
        have := hmax _ ⟨w k, hne, hww k⟩
        have hk' : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
        have hij' : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
        have key : ∑ l : Fin n, ((n : ℤ) - ((l : ℕ) : ℤ)) * ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l)
            = ∑ l : Fin n, ((n : ℤ) - ((l : ℕ) : ℤ)) * μ l + k * (((n : ℤ) - ((i : ℕ) : ℤ)) - ((n : ℤ) - ((j : ℕ) : ℤ))) := by
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
            mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
          ring
        rw [key] at this
        nlinarith
      rw [hsum s C hC, Finset.sum_eq_single 0 (fun k _ hk => by rw [hz k hk, smul_zero]) (by simp), hw0, pow_zero, one_smul]
  obtain ⟨D, U, rfl, hD, hDd, hUb, hU1⟩ := GlobalTheory.T.GL_upperTriangular_eq_diagonal_mul_unitriangular' n B hB
  rw [hΦ.mul, ← mulVec_mulVec, hU U hUb hU1, hvw D hD]
  simp only [hDd]

end GlobalTheory.AlgWtHW
