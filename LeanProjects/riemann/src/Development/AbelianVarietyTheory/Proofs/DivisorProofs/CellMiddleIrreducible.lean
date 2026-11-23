import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

namespace GlobalTheory.IndLineGL

theorem cellMid_isIrreducible_of_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.ThK.KP → ∀ (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) → (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) →
    ∀ b : SizeMatrix (Two (Fin a) (Fin a')) (fun j : Fin 3 => Fin (blk3 m j)), b.1 false 0 = b.1 false 2 →
      (cellMid k α₀ β₀ b.1).IsIrreducible := by
  intro k _ _ _ _ hK a a' m α₀ β₀ hαs hβs hαu hβu b h
  have c0 := b.2.2 0
  have c2 := b.2.2 2
  simp only [Fintype.card_fin, Fintype.sum_bool] at c0 c2
  have e0 : blk3 m 0 = 1 := rfl
  have e2 : blk3 m 2 = 1 := rfl
  have ht : b.1 true 0 = b.1 true 2 := by omega
  have z0 : (((b.1 false 0 : ℕ) : ℂ) - (b.1 false 2 : ℕ)) / 2 = 0 := by rw [h, sub_self, zero_div]
  have z1 : (((b.1 true 0 : ℕ) : ℂ) - (b.1 true 2 : ℕ)) / 2 = 0 := by rw [ht, sub_self, zero_div]
  unfold cellMid
  rw [z0, z1, absPow_zero, mul_one, mul_one]
  exact GlobalTheory.Published.BernsteinUnitaryProductIrreducible.prod₂_detRep hK.base.bernsteinUnitaryProductIrreducible _
    (GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp _ hαs hαu).1
    (GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp _ hαs hαu).2.1
    (GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp _ hαs hαu).2.2 hβs hβu

end GlobalTheory.IndLineGL
