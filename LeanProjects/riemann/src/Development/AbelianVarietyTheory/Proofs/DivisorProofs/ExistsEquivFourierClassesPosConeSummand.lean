import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.Div.QFibre

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

theorem unit_mul_mem (𝔞 : Frac F) (ε : (𝓞 F)ˣ) {x : F} (hx : x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ((ε : 𝓞 F) : F) * x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hx
  rw [Algebra.smul_def] at this
  exact this

def toQ (𝔞 𝔟 : Frac F) (x : Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) : Quotient (qRel 𝔞 𝔟) :=
  Quotient.mk _ ⟨(x.2.1, rep x.1), x.2.2.1, rep_mem x.1, x.2.2.2⟩

theorem toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨β, ν, hν⟩ ⟨β', ν', hν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  simp only at h1 h2
  have hβ : β = β' := by
    rw [← Quotient.out_eq β, ← Quotient.out_eq β']
    exact Quotient.sound ⟨ε, h2⟩
  subst hβ
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h0 := rep_ne_zero β
    have : (((ε : 𝓞 F) : F) - 1) * rep β = 0 := by unfold rep at h2 ⊢; rw [sub_mul, ← h2]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : (⟨ν, hν⟩ : posCone 𝔞 (rep β)) = ⟨ν', hν'⟩ := Subtype.ext h1.symm
  rw [this]

theorem exists_emb [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact ⟨(IsTotallyReal.complexEmbedding_isReal w.embedding).embedding⟩

theorem toQ_surjective [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro c
  induction c using Quotient.ind with
  | _ p =>
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨τ⟩ := exists_emb (F := F)
    have := hpos τ; simp at this
  let β : NzCls 𝔟 := Quotient.mk _ ⟨b, hb, hb0⟩
  obtain ⟨ε, hε⟩ : (unitRel 𝔟).r (Quotient.out β) ⟨b, hb, hb0⟩ := Quotient.exact (Quotient.out_eq β)
  have h4 := unit_inv_mul ε
  have hrep : rep β = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * b := by
    unfold rep; simp only at hε; rw [hε, ← mul_assoc, h4, one_mul]
  have hprod : ((ε : 𝓞 F) : F) * ν * rep β = ν * b := by
    rw [hrep]; linear_combination (ν * b) * h4
  refine ⟨⟨β, ((ε : 𝓞 F) : F) * ν, unit_mul_mem 𝔞 ε hν, fun τ => by rw [hprod]; exact hpos τ⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, ?_⟩
  · show ν = _ * (((ε : 𝓞 F) : F) * ν)
    rw [← mul_assoc, h4, one_mul]
  · show b = ((ε : 𝓞 F) : F) * rep β
    rw [hrep, ← mul_assoc, mul_comm ((ε : 𝓞 F) : F), h4, one_mul]

theorem qFibres : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)) ≃ Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟),
      ∀ (k : ℕ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (e x) = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (x.2.1, GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  intro F _ _ _ 𝔞 𝔟
  refine ⟨Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩, fun k z x => ?_⟩
  exact qClass_mk 𝔞 𝔟 k z _

end GlobalTheory.Div.QFibre
