import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing

noncomputable section

open Matrix GlobalTheory.SUCong

namespace GlobalTheory.ResGlue

variable {A : Type} [CommRing A]

theorem red_mem {S : Subring A} {ϖ a : A} (h : a ∈ S) :
    red S ϖ a = Ideal.Quotient.mk (piIdeal S ϖ) ⟨a, h⟩ := by
  unfold red; rw [dif_pos h]

theorem red_add' {S : Subring A} {ϖ a b : A} (ha : a ∈ S) (hb : b ∈ S) :
    red S ϖ (a + b) = red S ϖ a + red S ϖ b := by
  rw [red_mem ha, red_mem hb, red_mem (add_mem ha hb), ← map_add]; rfl

theorem red_mul' {S : Subring A} {ϖ a b : A} (ha : a ∈ S) (hb : b ∈ S) :
    red S ϖ (a * b) = red S ϖ a * red S ϖ b := by
  rw [red_mem ha, red_mem hb, red_mem (mul_mem ha hb), ← map_mul]; rfl

theorem red_sub' {S : Subring A} {ϖ a b : A} (ha : a ∈ S) (hb : b ∈ S) :
    red S ϖ (a - b) = red S ϖ a - red S ϖ b := by
  rw [red_mem ha, red_mem hb, red_mem (sub_mem ha hb), ← map_sub]; rfl

theorem red_neg' {S : Subring A} {ϖ a : A} (ha : a ∈ S) :
    red S ϖ (-a) = -red S ϖ a := by
  rw [red_mem ha, red_mem (neg_mem ha), ← map_neg]; rfl

theorem red_one' (S : Subring A) (ϖ : A) : red S ϖ 1 = 1 := by
  rw [red_mem (one_mem S), ← map_one (Ideal.Quotient.mk (piIdeal S ϖ))]; rfl

theorem red_zero' (S : Subring A) (ϖ : A) : red S ϖ 0 = 0 := by
  rw [red_mem (zero_mem S), ← map_zero (Ideal.Quotient.mk (piIdeal S ϖ))]; rfl

theorem red_surj (S : Subring A) (ϖ : A) (x : Res S ϖ) : ∃ s ∈ S, x = red S ϖ s := by
  obtain ⟨⟨s, hs⟩, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨s, hs, (red_mem hs).symm⟩

theorem red_pi {S : Subring A} {ϖ s : A} (hϖ : ϖ ∈ S) (hs : s ∈ S) : red S ϖ (ϖ * s) = 0 := by
  rw [red_mem (mul_mem hϖ hs), Ideal.Quotient.eq_zero_iff_mem]
  have e : (⟨ϖ * s, mul_mem hϖ hs⟩ : S) = ⟨ϖ, hϖ⟩ * ⟨s, hs⟩ := rfl
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

def fixRes (S : Subring A) (σ : A →+* A) (ϖ : A) : Subring (Res S ϖ) where
  carrier := {x | ∃ a ∈ S, σ a = a ∧ x = red S ϖ a}
  zero_mem' := ⟨0, zero_mem _, map_zero σ, (red_zero' S ϖ).symm⟩
  one_mem' := ⟨1, one_mem _, map_one σ, (red_one' S ϖ).symm⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, hσa, rfl⟩ ⟨b, hb, hσb, rfl⟩
    exact ⟨a + b, add_mem ha hb, by rw [map_add, hσa, hσb], (red_add' ha hb).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, hσa, rfl⟩ ⟨b, hb, hσb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, by rw [map_mul, hσa, hσb], (red_mul' ha hb).symm⟩
  neg_mem' := by
    rintro _ ⟨a, ha, hσa, rfl⟩
    exact ⟨-a, neg_mem ha, by rw [map_neg, hσa], (red_neg' ha).symm⟩

theorem resGlue : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A)
    (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q : ℕ) (τ : Res S ϖ →+* Res S ϖ),
    GoodRing S σ ϖ q → GoodForm S σ H → (∀ a ∈ S, τ (red S ϖ a) = red S ϖ (σ a)) →
    ∃ k : Subring (Res S ϖ), ∃ w : Res S ϖ, ∃ H' : Matrix n n (Res S ϖ), (∀ x ∈ k, τ x = x) ∧
      w + τ w = 1 ∧ IsUnit (w - τ w) ∧ (∀ x : Res S ϖ, ∃ a ∈ k, ∃ b ∈ k, x = a + b * w) ∧
      (∀ x ∈ k, x ≠ 0 → ∃ y ∈ k, x * y = 1) ∧ Nat.card k = q ∧
      Formalism.UG.cT τ (H.map (red S ϖ)) = H.map (red S ϖ) ∧ H.map (red S ϖ) * H' = 1 := by
  intro A _ n _ _ S σ H ϖ q τ hG hF hτ
  obtain ⟨hinv, hS, hϖS, hσϖ, hnzd, ⟨w₀, hw₀S, hw1, ⟨u, huS, hu⟩, hdec⟩, hloc, hcard⟩ := hG
  obtain ⟨hH, hherm, H₁, hH₁, hHH₁⟩ := hF
  refine ⟨fixRes S σ ϖ, red S ϖ w₀, H₁.map (red S ϖ), ?_, ?_, ?_, ?_, ?_, hcard, ?_, ?_⟩
  · rintro _ ⟨a, ha, hσa, rfl⟩
    rw [hτ a ha, hσa]
  · rw [hτ w₀ hw₀S, ← red_add' hw₀S (hS w₀ hw₀S), hw1, red_one']
  · refine isUnit_iff_exists_inv.mpr ⟨red S ϖ u, ?_⟩
    rw [hτ w₀ hw₀S, ← red_sub' hw₀S (hS w₀ hw₀S), ← red_mul' (sub_mem hw₀S (hS w₀ hw₀S)) huS,
      hu, red_one']
  · intro x
    obtain ⟨s, hs, rfl⟩ := red_surj S ϖ x
    obtain ⟨a, ha, b, hb, hσa, hσb, rfl⟩ := hdec s hs
    refine ⟨red S ϖ a, ⟨a, ha, hσa, rfl⟩, red S ϖ b, ⟨b, hb, hσb, rfl⟩, ?_⟩
    rw [red_add' ha (mul_mem hb hw₀S), red_mul' hb hw₀S]
  · rintro _ ⟨a, ha, hσa, rfl⟩ hne
    have hnp : ¬ InPow S ϖ 1 a := by
      rintro ⟨s, hs, rfl⟩
      exact hne (by rw [pow_one]; exact red_pi hϖS hs)
    obtain ⟨b, hb, hab⟩ := hloc a ha hσa hnp
    have hσb : σ b = b := by
      have h1 : a * σ b = 1 := by rw [← hσa, ← map_mul, hab, map_one]
      calc σ b = σ b * (a * b) := by rw [hab, mul_one]
        _ = (a * σ b) * b := by ring
        _ = b := by rw [h1, one_mul]
    exact ⟨red S ϖ b, ⟨b, hb, hσb, rfl⟩, by rw [← red_mul' ha hb, hab, red_one']⟩
  · ext i j
    have e := congrFun (congrFun hherm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at e ⊢
    rw [hτ _ (hH j i), e]
  · let HS : Matrix n n S := fun i j => ⟨H i j, hH i j⟩
    let HS₁ : Matrix n n S := fun i j => ⟨H₁ i j, hH₁ i j⟩
    have hone : HS * HS₁ = 1 := by
      have e : (HS * HS₁).map S.subtype = (1 : Matrix n n S).map S.subtype := by
        rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hHH₁
      ext i j
      exact congrFun (congrFun e i) j
    have e1 : H.map (red S ϖ) = HS.map (Ideal.Quotient.mk (piIdeal S ϖ)) := by
      ext i j; exact red_mem (hH i j)
    have e2 : H₁.map (red S ϖ) = HS₁.map (Ideal.Quotient.mk (piIdeal S ϖ)) := by
      ext i j; exact red_mem (hH₁ i j)
    rw [e1, e2, ← Matrix.map_mul, hone, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ResGlue
