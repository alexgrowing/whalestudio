import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.DualCount

theorem relIndex_le_of_selfDual (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hanti : ∀ x y, ω x y = -ω y x)
    (h₁ : ∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n)
    (h₂ : ∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n)
    (hfin : Λ₁.relIndex Λ₂ ≠ 0) : Λ₂.relIndex Λ₁ ≤ Λ₁.relIndex Λ₂ := by
  classical
  have hadd' : ∀ x y z, ω x (y + z) = ω x y + ω x z := by
    intro x y z
    rw [hanti x (y + z), hadd, hanti x y, hanti x z]; ring
  have hsub : ∀ x y z, ω (x - y) z = ω x z - ω y z := by
    intro x y z
    have := hadd (x - y) y z
    rw [sub_add_cancel] at this
    linarith
  have hint : ∀ r : ℝ, ((r : ℝ) : UnitAddCircle) = 0 ↔ ∃ n : ℤ, r = n := by
    intro r
    rw [AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
  let φ : H → (Λ₂ →+ UnitAddCircle) := fun x =>
    AddMonoidHom.mk' (fun y => ((ω x y : ℝ) : UnitAddCircle)) (by
      intro a b
      simp only [AddSubgroup.coe_add, hadd', AddCircle.coe_add])
  have hφ : ∀ x : Λ₁, Λ₁.addSubgroupOf Λ₂ ≤ (φ x).ker := by
    intro x y hy
    rw [AddMonoidHom.mem_ker]
    exact (hint _).2 ((h₁ x).1 x.2 y (AddSubgroup.mem_addSubgroupOf.1 hy))
  let ψ : Λ₁ → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ →+ UnitAddCircle) := fun x =>
    QuotientAddGroup.lift _ (φ x) (hφ x)
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let χ : Λ₁ → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) Circle := fun x =>
    (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom (ψ x)
  have hχ : ∀ a b : Λ₁, χ a = χ b → ((a : H) - b) ∈ Λ₂ := by
    intro a b hab
    rw [h₂]
    intro y hy
    have h := DFunLike.congr_fun hab (QuotientAddGroup.mk ⟨y, hy⟩)
    have h' : AddCircle.toCircle (((ω a y : ℝ)) : UnitAddCircle)
        = AddCircle.toCircle (((ω b y : ℝ)) : UnitAddCircle) := h
    have h'' := AddCircle.injective_toCircle (T := 1) one_ne_zero h'
    rw [← hint, hsub, AddCircle.coe_sub, h'', sub_self]
  haveI hG : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hfin
  haveI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _
  let f : (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ := fun q =>
    AddChar.circleEquivComplex (χ q.out)
  have hf : Function.Injective f := by
    intro p q hpq
    have h := hχ _ _ (AddChar.circleEquivComplex.injective hpq)
    rw [← QuotientAddGroup.out_eq' p, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_addSubgroupOf]
    exact h
  have hle := Nat.card_le_card_of_injective f hf
  have hc : Nat.card (AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ)
      = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  rw [hc] at hle
  exact hle

theorem relIndex_eq_of_selfDual : ∀ (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H), (∀ x y z, ω (x + y) z = ω x z + ω y z) → (∀ x y, ω x y = -ω y x) →
    (∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n) → (∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n) →
    Λ₁.relIndex Λ₂ ≠ 0 → Λ₂.relIndex Λ₁ ≠ 0 → Λ₁.relIndex Λ₂ = Λ₂.relIndex Λ₁ := by
  intro H _ ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁ f₂
  exact le_antisymm (relIndex_le_of_selfDual H ω Λ₂ Λ₁ hadd hanti h₂ h₁ f₂)
    (relIndex_le_of_selfDual H ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁)

end GlobalTheory.MomT.DualCount
