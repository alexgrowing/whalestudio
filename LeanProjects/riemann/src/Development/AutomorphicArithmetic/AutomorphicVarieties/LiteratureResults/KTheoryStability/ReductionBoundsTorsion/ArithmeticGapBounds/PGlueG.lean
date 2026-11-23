import Mathlib

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.GlueG

theorem eq_of_mk_eq {Γ : Type} [Group Γ] (H : Subgroup Γ) {E : Type} (F : Γ → E)
    (hF : ∀ h ∈ H, ∀ γ, F (h * γ) = F γ) {x y : Γ}
    (hxy : (Quotient.mk (QuotientGroup.rightRel H) x) = Quotient.mk (QuotientGroup.rightRel H) y) :
    F x = F y := by
  have h1 : y * x⁻¹ ∈ H := QuotientGroup.rightRel_apply.1 (Quotient.exact hxy)
  have := hF _ h1 x
  rw [inv_mul_cancel_right] at this
  exact this.symm

theorem finsum_transfer {A Γ : Type} [Group A] [Group Γ] (ψ : A →* Γ) (H : Subgroup Γ) (C : Subgroup A)
    (hC : ∀ a, ψ a ∈ H ↔ a ∈ C) (hs : ∀ γ, ∃ a, γ * (ψ a)⁻¹ ∈ H)
    {E : Type} [AddCommMonoid E] (F : Γ → E) (hF : ∀ h ∈ H, ∀ γ, F (h * γ) = F γ) :
    ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F c.out =
        ∑ᶠ c : Quotient (QuotientGroup.rightRel C), F (ψ c.out) ∧ C.index = H.index := by
  have key : ∀ a b : A, (QuotientGroup.rightRel C) a b ↔ (QuotientGroup.rightRel H) (ψ a) (ψ b) := by
    intro a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, ← hC, map_mul, map_inv]
  let e0 : Quotient (QuotientGroup.rightRel C) → Quotient (QuotientGroup.rightRel H) :=
    Quotient.map' ψ fun a b h => (key a b).1 h
  have he0 : ∀ a, e0 (Quotient.mk _ a) = Quotient.mk _ (ψ a) := fun a => rfl
  have hbij : Function.Bijective e0 := by
    constructor
    · intro c c' hcc'
      induction c using Quotient.inductionOn
      induction c' using Quotient.inductionOn
      rw [he0, he0] at hcc'
      exact Quotient.sound ((key _ _).2 (Quotient.exact hcc'))
    · intro c
      induction c using Quotient.inductionOn with
      | h γ =>
        obtain ⟨a, ha⟩ := hs γ
        exact ⟨Quotient.mk _ a, by
          rw [he0]
          exact Quotient.sound (QuotientGroup.rightRel_apply.2 ha)⟩
  let e := Equiv.ofBijective e0 hbij
  constructor
  · rw [← finsum_comp_equiv e]
    refine finsum_congr fun c => ?_
    apply eq_of_mk_eq H F hF
    show Quotient.mk _ (e0 c).out = _
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  · unfold Subgroup.index
    rw [← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel C),
      ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)]
    exact Nat.card_congr e

theorem finsum_mul_right {Γ : Type} [Group Γ] (H : Subgroup Γ) {E : Type} [AddCommMonoid E] (F : Γ → E)
    (hF : ∀ h ∈ H, ∀ γ, F (h * γ) = F γ) (γ₀ : Γ) :
    ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F (c.out * γ₀) =
      ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F c.out := by
  have key : ∀ a b : Γ, (QuotientGroup.rightRel H) a b ↔
      (QuotientGroup.rightRel H) ((Equiv.mulRight γ₀) a) ((Equiv.mulRight γ₀) b) := by
    intro a b
    simp only [QuotientGroup.rightRel_apply, Equiv.coe_mulRight, mul_inv_rev, mul_assoc,
      mul_inv_cancel_left]
  let e : Quotient (QuotientGroup.rightRel H) ≃ Quotient (QuotientGroup.rightRel H) :=
    Quotient.congr (Equiv.mulRight γ₀) key
  have h1 : ∀ c, F (e c).out = F (c.out * γ₀) := by
    intro c
    apply eq_of_mk_eq H F hF
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  calc ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F (c.out * γ₀)
      = ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F (e c).out := finsum_congr fun c => (h1 c).symm
    _ = _ := finsum_comp_equiv e (f := fun c => F c.out)

theorem continuous_finsum_quot {Γ X : Type} [Group Γ] [TopologicalSpace X] (H : Subgroup Γ) (hH : H.index ≠ 0)
    (F : Γ → X → ℝ) (hF : ∀ γ, Continuous (F γ)) :
    Continuous fun x => ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F c.out x := by
  have : H.FiniteIndex := ⟨hH⟩
  have : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  let _ := Fintype.ofFinite (Quotient (QuotientGroup.rightRel H))
  simp_rw [finsum_eq_sum_of_fintype]
  exact continuous_finsetSum _ fun c _ => hF _

theorem fund_conj {S : Type} [Group S] [MeasurableSpace S] [MeasurableMul S] (μ : Measure S)
    [μ.IsMulLeftInvariant] (G₁ G₂ : Subgroup S) (q : S) (hq : ∀ y, y ∈ G₂ ↔ q * y * q⁻¹ ∈ G₁) (D : Set S)
    (hD : IsFundamentalDomain G₁ D μ) :
    IsFundamentalDomain G₂ ((fun x => q * x) ⁻¹' D) μ ∧ μ ((fun x => q * x) ⁻¹' D) = μ D ∧
      ∀ u : S → ℝ, (IntegrableOn (fun x => u (q * x)) ((fun x => q * x) ⁻¹' D) μ ↔ IntegrableOn u D μ) ∧
        ∫ x in (fun x => q * x) ⁻¹' D, u (q * x) ∂μ = ∫ x in D, u x ∂μ := by
  have hmp : MeasurePreserving (fun x => q * x) μ μ := measurePreserving_mul_left μ q
  have hemb : MeasurableEmbedding (fun x => q * x) := (MeasurableEquiv.mulLeft q).measurableEmbedding
  have hmem : ∀ g : G₁, q⁻¹ * (g : S) * q ∈ G₂ := fun g => by
    rw [hq]
    simp [mul_assoc]
  let e : G₁ → G₂ := fun g => ⟨q⁻¹ * g * q, hmem g⟩
  have hbij : Function.Bijective e := by
    constructor
    · intro g g' h
      have h' := congrArg (fun x : G₂ => (x : S)) h
      simp only [e, mul_left_inj, mul_right_inj] at h'
      exact Subtype.ext h'
    · intro h
      refine ⟨⟨q * h * q⁻¹, (hq h).1 h.2⟩, Subtype.ext ?_⟩
      simp [e, mul_assoc]
  refine ⟨hD.preimage_of_equiv hmp.quasiMeasurePreserving hbij ?_, measure_preimage_mul μ q D, fun u =>
    ⟨hmp.integrableOn_comp_preimage hemb, hmp.setIntegral_preimage_emb hemb u D⟩⟩
  intro g x
  simp [e, Subgroup.smul_def, mul_assoc]

end PositivityTheory.KB.SpectralGap.GlueG

end
