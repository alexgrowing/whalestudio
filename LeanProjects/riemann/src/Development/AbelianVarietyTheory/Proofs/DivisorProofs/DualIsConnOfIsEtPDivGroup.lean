import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualConvPowPrimePowApplyPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFiniteStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem PDivGroup.dual_isConn_of_isEt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) : G.IsEt → G.dual.IsConn := by
  intro hG n χ hχ
  have : IsReduced (G.A n) := hG n
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p

  have roots : ∀ r : ℕ, ∀ a : G.A n, ∃ b : G.A n, a = b ^ p ^ r := by
    intro r
    induction r with
    | zero => exact fun a => ⟨a, by simp⟩
    | succ r ih =>
      intro a
      obtain ⟨c, rfl⟩ := ih a
      obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (G.A n) c
      exact ⟨b, by rw [← pow_mul, pow_succ, mul_comm]⟩

  have h1 : χ 1 = 0 := by
    have hc := (RingHom.mem_ker).1 hχ
    exact hc
  refine ⟨p ^ n, ?_⟩
  apply CartierDual.ext_apply
  intro a
  obtain ⟨b, rfl⟩ := roots n a
  rw [GlobalTheory.T.cartierDual_convPow_primePow_apply_pow p k hp G n n χ b, PDivGroup.mulBy_pow_self, Algebra.algebraMap_eq_smul_one,
    map_smul, h1, smul_zero, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  rfl

end GlobalTheory
