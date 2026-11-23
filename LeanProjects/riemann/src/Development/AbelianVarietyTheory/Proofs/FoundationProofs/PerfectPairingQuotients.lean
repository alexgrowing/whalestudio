import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem exists_addChar_quotient {G : Type} [AddCommGroup G] (H : AddSubgroup G) (f : G → ℂ)
    (h0 : f 0 = 1) (hadd : ∀ x y, f (x + y) = f x * f y) (hH : ∀ x ∈ H, f x = 1) :
    ∃ χ : AddChar (G ⧸ H) ℂ, ∀ g : G, χ (g : G ⧸ H) = f g := by
  have hout : ∀ g : G, f (Quotient.out (g : G ⧸ H)) = f g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hadd, hH _ h.2, mul_one]
  refine ⟨⟨fun q => f (Quotient.out q), ?_, ?_⟩, hout⟩
  · rw [← QuotientAddGroup.mk_zero, hout, h0]
  · intro a b
    induction a using QuotientAddGroup.induction_on
    induction b using QuotientAddGroup.induction_on
    rw [← QuotientAddGroup.mk_add, hout, hout, hout, hadd]

theorem exists_injective_addChar {G K : Type} [AddCommGroup G] [AddCommGroup K] (H : AddSubgroup G)
    (L : AddSubgroup K) (p : G → K → ℂ)
    (hl : ∀ x y z, p (x + y) z = p x z * p y z) (hr : ∀ x y z, p x (y + z) = p x y * p x z)
    (h0 : ∀ x, p x 0 = 1) (h0' : ∀ y, p 0 y = 1)
    (hH : ∀ g, g ∈ H ↔ ∀ k, p g k = 1) (hL : ∀ k ∈ L, ∀ g, p g k = 1) :
    ∃ Φ : G ⧸ H → AddChar (K ⧸ L) ℂ, Function.Injective Φ ∧
      ∀ (g : G) (k : K), Φ (g : G ⧸ H) (k : K ⧸ L) = p g k := by
  choose χ hχ using fun g : G =>
    exists_addChar_quotient L (p g) (h0 g) (hr g) (fun k hk => hL k hk g)
  have hout : ∀ (g : G) (k : K), p (Quotient.out (g : G ⧸ H)) k = p g k := by
    intro g k
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hl, (hH _).1 h.2, mul_one]
  have hΦ : ∀ (g : G) (k : K), χ (Quotient.out (g : G ⧸ H)) (k : K ⧸ L) = p g k := by
    intro g k
    rw [hχ, hout]
  refine ⟨fun q => χ (Quotient.out q), ?_, hΦ⟩
  intro a b hab
  induction a using QuotientAddGroup.induction_on with | _ a
  induction b using QuotientAddGroup.induction_on with | _ b
  rw [QuotientAddGroup.eq, hH]
  intro k
  have h1 : p a k = p b k := by
    rw [← hΦ, ← hΦ]
    exact congrArg (fun ψ : AddChar (K ⧸ L) ℂ => ψ (k : K ⧸ L)) hab
  rw [hl, ← h1, ← hl, neg_add_cancel, h0']

theorem perfect_pairing_quotients : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (S A T₀ T : AddSubgroup X), (∀ a ∈ A, a ∈ S ↔ ∀ t ∈ T, γ a t = 1) → (∀ t ∈ T, t ∈ T₀ ↔ ∀ a ∈ A, γ a t = 1) → T₀.relIndex T ≠ 0 → S.relIndex A = T₀.relIndex T ∧ (∀ y : X, (∀ a ∈ A, a ∈ S → γ a y = 1) → ∃ t ∈ T, ∀ a ∈ A, γ a y = γ a t) ∧ ∀ t ∈ T, (∑ᶠ q : A ⧸ S.addSubgroupOf A, γ ((Quotient.out q : A) : X) t) = if t ∈ T₀ then (S.relIndex A : ℂ) else 0 := by
  intro R X M _ _ _ _ _ σ w γ W h S A T₀ T hS hT hfin
  have hS' : ∀ a : A, a ∈ S.addSubgroupOf A ↔ ∀ t : T, γ a t = 1 := by
    intro a
    rw [AddSubgroup.mem_addSubgroupOf, hS a a.2]
    simp
  have hT' : ∀ t : T, t ∈ T₀.addSubgroupOf T ↔ ∀ a : A, γ a t = 1 := by
    intro t
    rw [AddSubgroup.mem_addSubgroupOf, hT t t.2]
    simp
  obtain ⟨Φ, hΦi, hΦ⟩ := exists_injective_addChar (S.addSubgroupOf A) (T₀.addSubgroupOf T)
    (fun a t => γ a t) (fun x y z => h.add_left _ _ _) (fun x y z => h.add_right _ _ _)
    (fun x => h.zero_right _) (fun x => h.zero_left _) hS' (fun k hk => (hT' k).1 hk)
  obtain ⟨Ψ, hΨi, hΨ⟩ := exists_injective_addChar (T₀.addSubgroupOf T) (S.addSubgroupOf A)
    (fun t a => γ a t) (fun x y z => h.add_right _ _ _) (fun x y z => h.add_left _ _ _)
    (fun x => h.zero_left _) (fun x => h.zero_right _) hT' (fun k hk => (hS' k).1 hk)
  haveI : Finite (T ⧸ T₀.addSubgroupOf T) := Nat.finite_of_card_ne_zero hfin
  haveI : Finite (A ⧸ S.addSubgroupOf A) := Finite.of_injective Φ hΦi
  letI := Fintype.ofFinite (T ⧸ T₀.addSubgroupOf T)
  letI := Fintype.ofFinite (A ⧸ S.addSubgroupOf A)
  have c1 := Fintype.card_le_of_injective Φ hΦi
  have c2 := Fintype.card_le_of_injective Ψ hΨi
  have c3 := c2
  rw [AddChar.card_eq] at c1 c2
  have hc : Fintype.card (A ⧸ S.addSubgroupOf A) = Fintype.card (T ⧸ T₀.addSubgroupOf T) :=
    le_antisymm c1 c2
  have eA : S.relIndex A = Fintype.card (A ⧸ S.addSubgroupOf A) := Nat.card_eq_fintype_card
  have eT : T₀.relIndex T = Fintype.card (T ⧸ T₀.addSubgroupOf T) := Nat.card_eq_fintype_card
  refine ⟨by rw [eA, eT, hc], ?_, ?_⟩
  · intro y hy
    obtain ⟨χ, hχ⟩ := exists_addChar_quotient (S.addSubgroupOf A) (fun a : A => γ a y)
      (h.zero_left _) (fun a b => h.add_left _ _ _)
      (fun a ha => hy a a.2 (AddSubgroup.mem_addSubgroupOf.1 ha))
    have hb : Function.Bijective Ψ :=
      (Fintype.bijective_iff_injective_and_card Ψ).2 ⟨hΨi, by rw [AddChar.card_eq, hc]⟩
    obtain ⟨q, hq⟩ := hb.2 χ
    induction q using QuotientAddGroup.induction_on with | _ t
    refine ⟨t, t.2, fun a ha => ?_⟩
    have h1 := hΨ t ⟨a, ha⟩
    rw [hq, hχ] at h1
    exact h1
  · intro t ht
    rw [finsum_eq_sum_of_fintype]
    have h1 : ∀ q : A ⧸ S.addSubgroupOf A,
        γ ((Quotient.out q : A) : X) t = Ψ ((⟨t, ht⟩ : T) : T ⧸ T₀.addSubgroupOf T) q := by
      intro q
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [hΨ]
    rw [Finset.sum_congr rfl fun q _ => h1 q, AddChar.sum_eq_ite, eA]
    refine if_congr ?_ rfl rfl
    rw [hT t ht]
    constructor
    · intro h0 a ha
      have h2 := hΨ ⟨t, ht⟩ ⟨a, ha⟩
      rw [h0] at h2
      simpa using h2.symm
    · intro h0
      ext q
      rw [← h1, h0 _ (Quotient.out q).2]
      simp

end GlobalTheory.FinWeil
