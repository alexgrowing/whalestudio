import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnit
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem sum_act_upper_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (N l : ℕ) [Fact l.Prime] (q M : ℕ), 0 < q → Nat.Coprime q M → ∀ b : X.Fn l,
    (∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b) →
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] b =
      ∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b := by
  intro Ω _ _ _ ε X N l _ q M hq hqM b hb
  have hT : ∀ t : ℤ, X.act l !![1, t; 0, 1] b = b := by
    intro t
    let T : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hmem : T ∈ Gam N l := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [CongruenceSubgroup.Gamma1_mem]
        refine ⟨?_, ?_, ?_⟩ <;> simp [T]
      · rw [CongruenceSubgroup.Gamma0_mem]
        simp [T]
    exact hb T hmem
  have he : IsCoprime (M : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd_natCast_natCast] using hqM.symm
  exact (Tower.sum_act_upper_mul_unit X l b hT q (M : ℤ) hq he).symm

end GlobalTheory.KZ.ES
