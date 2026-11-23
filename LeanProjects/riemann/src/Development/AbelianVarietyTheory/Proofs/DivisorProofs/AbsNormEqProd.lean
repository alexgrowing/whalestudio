import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem phi_zero (w : ℂ) : phi 0 w = w⁻¹ ^ 2 := by
  simp [phi]

theorem hTrans_zero_neg (ν y : ℝ) : hTrans 0 ν (-y) = hTrans 0 (-ν) y := by
  unfold hTrans
  conv_lhs => rw [← MeasureTheory.integral_neg_eq_self]
  congr 1; funext t
  simp only [phi_zero, ofReal_neg]
  congr 1
  · rw [show -(t : ℂ) + -(y : ℂ) * I = -((t : ℂ) + (y : ℂ) * I) by ring, inv_neg, neg_sq]
  · congr 1; ring

theorem emb_nonempty [IsTotallyReal F] : Nonempty (Emb F) := by
  have : Nonempty (F →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := this
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

theorem abs_norm_eq_prod [IsTotallyReal F] (ν : F) :
    ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) = ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ) := by
  have h := prod_emb ν
  have h' : ((Algebra.norm ℚ ν : ℚ) : ℝ) = ∏ τ : Emb F, τ ν := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_prod, h]; push_cast; rfl
  rw [h', Finset.abs_prod, Complex.ofReal_prod]

end GlobalTheory.HeckeTwoExp

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

def toQ (𝔞 𝔟 : Frac F) : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → Quotient (qRel 𝔞 𝔟) :=
  fun s => Quotient.mk _ ⟨(s.2.1.1, s.1.out.1), s.2.1.2.1, s.1.out.2.1, s.2.2⟩

theorem toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨c, ν⟩ ⟨c', ν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  dsimp only at h1 h2
  have hc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨ε, h2⟩
  subst hc
  have hne : c.out.1 ≠ 0 := c.out.2.2
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h3 : (((ε : 𝓞 F) : F) - 1) * c.out.1 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : ν = ν' := Subtype.ext (Subtype.ext h1.symm)
  subst this
  rfl

theorem toQ_surjective [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p => ?_
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  obtain ⟨τ₀⟩ := emb_nonempty (F := F)
  have hνb : ν * b ≠ 0 := by
    intro h0; have := hpos τ₀; rw [h0, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hν0 : ν ≠ 0 := left_ne_zero_of_mul hνb
  set c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := Quotient.mk _ ⟨b, hb, hb0⟩ with hcdef
  obtain ⟨ε, hε⟩ := Quotient.exact (Quotient.out_eq c : Quotient.mk _ c.out = Quotient.mk _ ⟨b, hb, hb0⟩)
  dsimp only at hε
  have hmem : ((ε : 𝓞 F) : F) * ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
    have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hν
    rw [Algebra.smul_def] at this
    exact this
  have hne : ((ε : 𝓞 F) : F) * ν ≠ 0 := by
    refine mul_ne_zero ?_ hν0
    intro h0
    have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hprod : ((ε : 𝓞 F) : F) * ν * c.out.1 = ν * b := by rw [hε]; ring
  refine ⟨⟨c, ⟨⟨((ε : 𝓞 F) : F) * ν, hmem, hne⟩, fun τ => by rw [hprod]; exact hpos τ⟩⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, hε⟩
  show ν = _ * (((ε : 𝓞 F) : F) * ν)
  rw [← mul_assoc, unit_inv_mul, one_mul]

theorem tsum_qClass_eq [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hS : Summable (qClass 𝔞 𝔟 2 z)) :
    ∑' c, qClass 𝔞 𝔟 2 z c = ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F),
        if ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1) then qTerm 𝔞 2 z (ν.1, c.out.1) else 0 := by
  set e := Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩ with he
  have hS' : Summable (qClass 𝔞 𝔟 2 z ∘ e) := e.summable_iff.2 hS
  have h1 : ∑' c, qClass 𝔞 𝔟 2 z c = ∑' p, qClass 𝔞 𝔟 2 z (e p) := (e.tsum_eq _).symm
  have h2 : ∑' p, qClass 𝔞 𝔟 2 z (e p) = ∑' c, ∑' ν, qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) := hS'.tsum_sigma
  rw [h1, h2]
  refine tsum_congr fun c => ?_
  have h3 := tsum_subtype {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) | ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}
    (fun ν => qTerm 𝔞 2 z (ν.1, c.out.1))
  have h4 : ∀ ν : {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)},
      qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) = qTerm 𝔞 2 z (ν.1.1, c.out.1) := fun ν => by
    rw [he]; exact qClass_mk 𝔞 𝔟 2 z _
  rw [tsum_congr h4]
  refine h3.trans (tsum_congr fun ν => ?_)
  rw [Set.indicator_apply]
  rfl

end GlobalTheory.HeckeTwoExp

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem kFac_zero_mul : kFac F 0 * (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) = 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * (-4 * (Real.pi : ℂ) ^ 2) = 1 := by
    rw [inv_pow, mul_pow, mul_pow, I_sq]
    field_simp
    ring
  unfold kFac
  simp only [mul_zero, cpow_zero, mul_one, Finset.prod_const, Finset.card_univ]
  rw [← mul_pow, h1, one_pow]

theorem dF_pos : 0 < dF F := abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero F))

theorem nrm_ne_zero (𝔞 : Frac F) : nrm 𝔞 ≠ 0 := by
  unfold nrm
  rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact 𝔞.ne_zero

end GlobalTheory.HeckeTwoExp
