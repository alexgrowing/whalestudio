import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq
open GlobalTheory.InertZeta Formalism.UG

namespace GlobalTheory.CompanionTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem traceZero_eq_map {σ : L →+* L} {c : L} (hc : c ≠ 0) (hσ : σ c = c) :
    traceZero σ c =
      ((intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker).map (AddMonoidHom.mulLeft c⁻¹) := by
  ext x
  rw [mem_traceZero, AddSubgroup.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨c * x, AddSubgroup.mem_inf.2 ⟨h1, ?_⟩, by simp [hc]⟩
    rw [AddMonoidHom.mem_ker]
    show σ (c * x) + c * x = 0
    rw [map_mul, hσ, ← mul_add, h2, mul_zero]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hy
    rw [AddMonoidHom.mem_ker] at h2
    have h2' : σ y + y = 0 := h2
    have hi : σ c⁻¹ = c⁻¹ := by rw [map_inv₀, hσ]
    refine ⟨?_, ?_⟩
    · show c * (c⁻¹ * y) ∈ intL L
      rw [mul_inv_cancel_left₀ hc]
      exact h1
    · show σ (c⁻¹ * y) + c⁻¹ * y = 0
      rw [map_mul, hi, ← mul_add, h2', mul_zero]

theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hbase := GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex GlobalTheory.SatakeWeyl.intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, hv, -, -, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  have hϖ1 : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv', ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have hS : ∀ f : ℕ, traceZero σ (ϖ ^ f) = T.map (AddMonoidHom.mulLeft (ϖ ^ f)⁻¹) := fun f =>
    traceZero_eq_map (pow_ne_zero f h0) (by rw [map_pow, hϖ])
  have hmono : ∀ f : ℕ, traceZero σ (ϖ ^ f) ≤ traceZero σ (ϖ ^ (f + 1)) := by
    intro f x hx
    obtain ⟨h1, h2⟩ := mem_traceZero.1 hx
    refine mem_traceZero.2 ⟨?_, h2⟩
    rw [pow_succ', mul_assoc]
    exact mul_mem hϖ1 h1
  have hstep : ∀ f : ℕ, (traceZero σ (ϖ ^ f)).relIndex (traceZero σ (ϖ ^ (f + 1))) = q := by
    intro f
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ (f + 1))⁻¹) :=
      mul_right_injective₀ (inv_ne_zero (pow_ne_zero _ h0))
    have e : T.map (AddMonoidHom.mulLeft (ϖ ^ f)⁻¹) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ (f + 1))⁻¹) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨ϖ * y, ⟨y, hy, rfl⟩, ?_⟩
        field_simp
        ring
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        field_simp
        ring
    rw [hS f, hS (f + 1), e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hbase
  induction f with
  | zero =>
    rw [pow_zero, pow_zero, AddSubgroup.relIndex_self]
  | succ f ih =>
    have hle : traceZero σ 1 ≤ traceZero σ (ϖ ^ f) := by
      clear ih
      induction f with
      | zero => rw [pow_zero]
      | succ f ih => exact ih.trans (hmono f)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle (hmono f), ih, hstep, pow_succ]

end GlobalTheory.CompanionTheory.InertZeta
