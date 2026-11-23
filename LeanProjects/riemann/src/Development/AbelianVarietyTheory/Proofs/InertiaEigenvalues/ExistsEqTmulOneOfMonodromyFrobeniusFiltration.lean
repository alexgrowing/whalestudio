import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisInclStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableCommStatement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_eq_tmul_one_of_mon_phi_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  intro l _ P AI T ι hι K V _ _ z hN hφ hF
  obtain ⟨w, rfl⟩ := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V z).mp hN
  rw [GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V w] at hφ
  have hw := crisIncl_injective P hφ
  have key : ∀ x : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V x) =
      ιV (P.PD K) (LL := ℚ_[l]) (V := V) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ιV, hι, P.PD_ι]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key] at hF
  obtain ⟨v, rfl⟩ := (GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K ℚ_[l] V).2 w hw hF
  exact ⟨v, by rw [crisIncl_tmul, Polynomial.C_1]⟩

end GlobalTheory.PMon
