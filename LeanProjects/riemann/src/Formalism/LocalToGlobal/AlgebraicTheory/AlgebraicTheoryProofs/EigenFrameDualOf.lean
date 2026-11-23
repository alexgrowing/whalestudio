import Formalism.LocalToGlobal.AlgebraicTheory.StatementEig
import ReciprocityTheory.EigenFrames.EigenSt

noncomputable section
open scoped BigOperators
open NumberField

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.GD (InMul frameM)
open Formalism.L2.Col (Fields Sp)
open Formalism.L2.Ker (Amb DVar)

namespace CapelliMinorMembership

theorem norm_natCast (p : ℕ) [Fact p.Prime] {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have hq : ‖(N : ℚ_[p])‖ = 1 := by
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 h)
  have e1 : ‖(N : PadicAlgCl p)‖ = 1 := by
    rw [← hq, ← PadicAlgCl.norm_extends]
    simp
  rw [← e1, ← PadicComplex.norm_extends]
  simp

end CapelliMinorMembership

theorem eigenFrameDual_of (h : ReciprocityTheory.EigenFramesTheory.EigenFrameDual.{0, 0}) : EigenFrameDual := by
  intro E _ _ p _ ι hd τ₀
  exact h p E _ (NumberField.RingOfIntegers.basis E) ι hd τ₀

theorem CapelliMinorMembership.key_term {X : Fields} (A : Amb X) {a b : ℕ} {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n₀ : ℕ}
    (hn0 : (n₀ : ℂ_[p]) ≠ 0) (r : X.Tau → Module.Free.ChooseBasisIndex ℤ (𝓞 X.E) → ℂ_[p])
    (τ₁ τ : X.Tau) (β₁ β' β : Fin b) (α₁ α' α : Fin a) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 X.E)) :
    (ι : ℂ →+* ℂ_[p]) (((n₀ : ℂ) • vecE A.σ₀ ((NumberField.RingOfIntegers.basis X.E i : 𝓞 X.E) : X.E) β α)
        (τ₁, β₁, α₁)) *
      (if β = β' ∧ α = α' then ι (A.cD τ) * r τ i * (n₀ : ℂ_[p])⁻¹ else 0) =
    if α = α₁ then (if β = β₁ then
      (if β₁ = β' ∧ α₁ = α' then ι (A.cD τ) *
        (r τ i * ι (X.embC A.σ₀ τ₁ ((NumberField.RingOfIntegers.basis X.E i : 𝓞 X.E) : X.E))) else 0)
      else 0) else 0 := by
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hα : α = α₁
  · subst hα
    by_cases hβ : β = β₁
    · subst hβ
      by_cases h' : β = β' ∧ α = α'
      · simp only [vecE, h', and_self, if_true]
        rw [map_mul, map_natCast]
        field_simp
        simp only [RingEquiv.coe_toRingHom]
        ring
      · simp [vecE, h']
    · simp [vecE, hβ, Ne.symm hβ]
  · simp [vecE, hα, Ne.symm hα]

theorem CapelliMinorMembership.collapse {K κ B C : Type} [AddCommMonoid K] [Fintype κ] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (g : κ → K) (β₁ : B) (α₁ : C) :
    ∑ i, ∑ β : B, ∑ α : C, (if α = α₁ then (if β = β₁ then g i else 0) else 0) = ∑ i, g i := by
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem kerFrame_of (h : EigenFrameDual) : KerFrame := by
  intro X A a b N N' L p _ ι hd hinj hcD hn
  obtain ⟨n₀, hn₀, hv⟩ := hn
  choose r hr1 hr2 using fun τ : X.Tau => h X.E p ι hd (X.embC A.σ₀ τ)
  have hn0 : (n₀ : ℂ_[p]) ≠ 0 := by
    intro h0
    have := CapelliMinorMembership.norm_natCast p hn₀
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  refine ⟨Module.Free.ChooseBasisIndex ℤ (𝓞 X.E) × Fin b × Fin a, inferInstance,
    fun j => (n₀ : ℂ) • vecE A.σ₀ ((NumberField.RingOfIntegers.basis X.E j.1 : 𝓞 X.E) : X.E) j.2.1 j.2.2,
    fun j k => if j.2.1 = k.2.1 ∧ j.2.2 = k.2.2 then ι (A.cD k.1) * r k.1 j.1 * (n₀ : ℂ_[p])⁻¹ else 0,
    fun j => hv _ _ _, ?_, ?_⟩
  · intro j k
    dsimp only
    split_ifs
    · rw [norm_mul, norm_mul, norm_inv, CapelliMinorMembership.norm_natCast p hn₀, inv_one, mul_one]
      first
      | exact mul_le_one₀ (hcD _) (norm_nonneg _) (hr1 _ _)
      | nlinarith [norm_nonneg (ι (A.cD k.1)), norm_nonneg (r k.1 j.1), hcD k.1, hr1 k.1 j.1]
    · simp
  · intro i k
    obtain ⟨τ₁, β₁, α₁⟩ := i
    obtain ⟨τ, β', α'⟩ := k
    unfold frameM
    simp only [Fintype.sum_prod_type]
    simp only [CapelliMinorMembership.key_term A ι hn0 r]
    refine (CapelliMinorMembership.collapse _ β₁ α₁).trans ?_
    by_cases hc : β₁ = β' ∧ α₁ = α'
    · refine (Finset.sum_congr rfl (fun i _ => if_pos hc)).trans ?_
      rw [← Finset.mul_sum, hr2 τ (X.embC A.σ₀ τ₁)]
      obtain ⟨rfl, rfl⟩ := hc
      by_cases ht : τ₁ = τ
      · subst ht
        simp
      · have hne : X.embC A.σ₀ τ₁ ≠ X.embC A.σ₀ τ := fun e => ht (hinj e)
        rw [if_neg hne, mul_zero, if_neg]
        intro he
        exact ht (Prod.mk.inj he).1
    · refine (Finset.sum_congr rfl (fun i _ => if_neg hc)).trans ?_
      rw [Finset.sum_const_zero, if_neg]
      intro he
      have h2 := (Prod.mk.inj he).2
      exact hc ⟨(Prod.mk.inj h2).1, (Prod.mk.inj h2).2⟩

end Formalism.L2.AlgTh
