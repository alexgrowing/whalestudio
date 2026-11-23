import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulNormLeOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes.Denom

variable (p : ℕ) [Fact p.Prime]

theorem exists_pow_mul_norm_le_one (y : PadicAlgCl p) : ∃ k : ℕ, ‖(p : PadicAlgCl p) ^ k * y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one
  | exact _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one
  | (apply _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one ..)

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

theorem inclK_mem (a : K) (ha : ‖(a : PadicAlgCl p)‖ ≤ 1) : inclK p K r a ∈ intKQ p K r :=
  Subring.subset_closure (Or.inl ⟨⟨a, (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 ha⟩, rfl⟩)

theorem inclQ_mem (b : Qr p r) (hb : ‖(b : PadicAlgCl p)‖ ≤ 1) : inclQ p K r b ∈ intKQ p K r :=
  Subring.subset_closure (Or.inr ⟨⟨b, (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 hb⟩, rfl⟩)

theorem aux (x : K ⊗[ℚ_[p]] Qr p r) :
    ∃ k : ℕ, (p : K ⊗[ℚ_[p]] Qr p r) ^ k * x ∈ intKQ p K r := by
  have hp : ∀ m : ℕ, (p : K ⊗[ℚ_[p]] Qr p r) ^ m ∈ intKQ p K r := fun m => pow_mem (natCast_mem _ p) m
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [mul_zero]; exact (intKQ p K r).zero_mem⟩
  | tmul a b =>
    obtain ⟨k, hk⟩ := exists_pow_mul_norm_le_one p (a : PadicAlgCl p)
    obtain ⟨l, hl⟩ := exists_pow_mul_norm_le_one p (b : PadicAlgCl p)
    refine ⟨k + l, ?_⟩
    have e : (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (a ⊗ₜ[ℚ_[p]] b) =
        ((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b) := by
      calc (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (a ⊗ₜ[ℚ_[p]] b)
          = (Algebra.TensorProduct.includeLeft (R := ℚ_[p]) (S := ℚ_[p]) (B := Qr p r) ((p : K) ^ k)) *
            (Algebra.TensorProduct.includeRight (R := ℚ_[p]) (A := K) ((p : Qr p r) ^ l)) * (a ⊗ₜ[ℚ_[p]] b) := by
            simp only [map_pow, map_natCast, pow_add]
        _ = _ := by
            simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    have hm := mul_mem (inclK_mem p K r ((p : K) ^ k * a) (by simpa using hk))
      (inclQ_mem p K r ((p : Qr p r) ^ l * b) (by simpa using hl))
    have e2 : inclK p K r ((p : K) ^ k * a) * inclQ p K r ((p : Qr p r) ^ l * b) =
        ((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b) := by
      change (((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [← e2]
    exact hm
  | add x y hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨k + l, ?_⟩
    have e : (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (x + y) =
        (p : K ⊗[ℚ_[p]] Qr p r) ^ l * ((p : K ⊗[ℚ_[p]] Qr p r) ^ k * x) +
          (p : K ⊗[ℚ_[p]] Qr p r) ^ k * ((p : K ⊗[ℚ_[p]] Qr p r) ^ l * y) := by
      ring
    rw [e]
    exact add_mem (mul_mem (hp l) hk) (mul_mem (hp k) hl)

end GlobalTheory.LKRes.Denom

namespace GlobalTheory.LKRes

theorem exists_pow_mul_mem_intKQ : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)
    (x : KQ p K r), ∃ k : ℕ, (p : KQ p K r) ^ k * x ∈ intKQ p K r :=
  fun p _ K r x => Denom.aux p K r x

end GlobalTheory.LKRes
