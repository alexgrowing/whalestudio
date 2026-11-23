import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisPer

theorem per_val {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (n : ℤ) :
    a n = a (((n : ZMod N).val : ℕ) : ℤ) := by
  have hp : Function.Periodic a (N : ℤ) := ha
  rw [ZMod.val_intCast]
  have := hp.int_mul (n / N) (n % N)
  simp only [Int.cast_id] at this
  rw [← this]
  congr 1
  have := Int.mul_ediv_add_emod n N
  linarith [mul_comm (N : ℤ) (n / N)]

theorem sum_range_zmod {N : ℕ} [NeZero N] (g : ZMod N → ℂ) :
    ∑ y ∈ Finset.range N, g (y : ZMod N) = ∑ z : ZMod N, g z := by
  refine Finset.sum_bij' (fun y _ => (y : ZMod N)) (fun z _ => z.val) (by simp)
    (fun z _ => by simpa using ZMod.val_lt z) (fun y hy => ZMod.val_cast_of_lt (Finset.mem_range.1 hy))
    (fun z _ => ZMod.natCast_zmod_val z) (fun _ _ => rfl)

def invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (y : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y))

theorem hat_invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) :
    hat (invF (N := N) a) d = a d := by
  unfold hat
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have e1 : ∀ y : ℕ, cexp (2 * π * Complex.I * (y * d) / N) = ZMod.stdAddChar ((y : ZMod N) * (d : ZMod N)) := by
    intro y
    have := ZMod.stdAddChar_coe (N := N) ((y : ℤ) * d)
    push_cast at this
    rw [← this]
  simp_rw [e1]
  rw [sum_range_zmod (fun z => invF a z * ZMod.stdAddChar (z * (d : ZMod N)))]
  unfold invF
  simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e2 : ∀ x y : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y)) * ZMod.stdAddChar (y * (d : ZMod N))
      = a (x.val : ℤ) * ZMod.stdAddChar (y * ((d : ZMod N) - x)) := by
    intro x y
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [e2]
  simp_rw [← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp_rw [ZMod.card, Nat.cast_ite, Nat.cast_zero, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (d : ZMod N) (fun x => a (x.val : ℤ) * (N : ℂ))]
  simp only [Finset.mem_univ, if_true]
  rw [← per_val a ha d]
  field_simp

theorem invF_twist {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) (c : ℂ)
    (hd : IsCoprime d (N : ℤ)) (hmul : ∀ x, a (x * d) = c * a x) (y : ZMod N) :
    invF (N := N) a y = c * invF (N := N) a (y * (d : ZMod N)) := by
  obtain ⟨u, v, huv⟩ := hd
  have hu : (u : ZMod N) * (d : ZMod N) = 1 := by
    have := congrArg (fun t : ℤ => (t : ZMod N)) huv
    simpa using this
  let U : (ZMod N)ˣ := ⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact hu, hu⟩
  unfold invF
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ x : ZMod N, c * ((N : ℂ)⁻¹ * (a (x.val : ℤ) * ZMod.stdAddChar (-(x * (y * (d : ZMod N))))))
      = (N : ℂ)⁻¹ * (a ((x * (d : ZMod N)).val : ℤ) * ZMod.stdAddChar (-((x * (d : ZMod N)) * y))) := by
    intro x
    have h1 : a ((x * (d : ZMod N)).val : ℤ) = c * a (x.val : ℤ) := by
      rw [← hmul, per_val a ha ((x.val : ℤ) * d)]
      congr 3
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h2 : -(x * (y * (d : ZMod N))) = -((x * (d : ZMod N)) * y) := by ring
    rw [h2]; ring
  exact (Fintype.sum_equiv (Units.mulRight U) _ _ e).symm

end GlobalTheory.EisPer

end

open GlobalTheory.EisPer in
theorem GlobalTheory.eis_periodic_weights : ∀ (j L₁ L₂ : ℕ) (a b χ₁ χ₂ : ℤ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → a 0 = 0 → (∀ x, a (x + L₁) = a x) → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ x, a (x * d) = χ₁ d * a x) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c a b) := by
  intro j L₁ L₂ a b χ₁ χ₂ hj hL₁ hL₂ ha0 ha hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hhat : hat (invF (N := L₁) a) = a := funext (hat_invF a ha)
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq j L₁ L₂ b χ₁ χ₂ (invF (N := L₁) a) hj hL₁ hL₂
    (by rw [hhat]; exact ha0) hb
    (fun d hd => ⟨fun y => invF_twist a ha d (χ₁ d)
      (by
        have : IsCoprime d ((L₁ : ℤ) * (L₂ : ℤ)) := by exact_mod_cast hd
        exact this.of_mul_right_left) (hχ d hd).1 y, (hχ d hd).2⟩) hpar
  exact ⟨c, by rw [hhat] at hc; exact hc⟩
