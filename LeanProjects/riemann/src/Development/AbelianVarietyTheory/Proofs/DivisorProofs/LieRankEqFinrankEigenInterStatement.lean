import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankEqFinrankEigenInter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_rank_eq_finrank_eigen_inter : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ) (σ : Λ →+* O), D.lieRank σ = Module.finrank C ↥(LinearMap.range (bC C D) ⊓ eig C (actT D) σ) := by
  first | exact @GlobalTheory.DetInv.lieRank_eq_finrank_range_bC_inf_eig | exact GlobalTheory.DetInv.lieRank_eq_finrank_range_bC_inf_eig | (intros; apply GlobalTheory.DetInv.lieRank_eq_finrank_range_bC_inf_eig <;> assumption)
