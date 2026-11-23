import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.DoubleCosetComm

variable {G : Type} [Group G]

def InDC (J : Subgroup G) (x g : G) : Prop := ∃ k₁ k₂ : J, g = (k₁ : G) * x * k₂

theorem InDC.mul {J : Subgroup G} {x g a b : G} (h : InDC J x g) (ha : a ∈ J) (hb : b ∈ J) :
    InDC J x (a * g * b) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨⟨a, ha⟩ * u, v * ⟨b, hb⟩, by simp [mul_assoc]⟩

theorem InDC.inv {J : Subgroup G} {x g : G} (h : InDC J x g) : InDC J x⁻¹ g⁻¹ := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨v⁻¹, u⁻¹, by simp [mul_assoc]⟩

open Classical in

theorem card_filter_le {J : Subgroup G} {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B)
    (P Q : G → Prop) (ψ : G → G) (h1 : ∀ a ∈ A, P a → InDC J y (ψ a))
    (h2 : ∀ a ∈ A, P a → ∀ k ∈ J, Q (ψ a * k))
    (h3 : ∀ a ∈ A, ∀ a' ∈ A, (ψ a)⁻¹ * ψ a' ∈ J → a⁻¹ * a' ∈ J) :
    (A.filter P).card ≤ (B.filter Q).card := by
  have hex : ∀ a : G, ∃ b : G, a ∈ A → P a → b ∈ B ∧ b⁻¹ * ψ a ∈ J := by
    intro a
    by_cases h : a ∈ A ∧ P a
    · obtain ⟨b, hb, -⟩ := hB.2 _ (h1 a h.1 h.2)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨1, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose r hr using hex
  refine Finset.card_le_card_of_injOn r ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨hb, hj⟩ := hr a ha.1 ha.2
    refine ⟨hb, ?_⟩
    have := h2 a ha.1 ha.2 _ (J.inv_mem hj)
    simpa [mul_assoc] using this
  · intro a ha a' ha' e
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ha'
    have hj := (hr a ha.1 ha.2).2
    have hj' := (hr a' ha'.1 ha'.2).2
    rw [← e] at hj'
    have h4 : (ψ a)⁻¹ * ψ a' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hj) hj'
    exact (hA.2 a' (hA.1 a' ha'.1)).unique ⟨ha.1, h3 a ha.1 a' ha'.1 h4⟩ ⟨ha'.1, by simp⟩

section Theta

variable {J L : Subgroup G} {θ : G → G}
  (hm : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (hi : ∀ x ∈ L, θ (θ x) = x)
  (hK : ∀ k ∈ J ⊓ L, θ k ∈ J) (hL : ∀ g ∈ L, θ g ∈ L)
  (hdc : ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)

include hm in
theorem theta_inv {g : G} (hg : g ∈ L) : θ g⁻¹ = (θ g)⁻¹ := by
  have h1 : θ 1 = 1 := by
    have h := hm 1 L.one_mem 1 L.one_mem
    rw [mul_one] at h
    have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h'
  apply eq_inv_of_mul_eq_one_left
  rw [← hm _ hg _ (L.inv_mem hg), mul_inv_cancel, h1]

include hm hi hK hL in
theorem theta_coset {a a' : G} (ha : a ∈ L) (ha' : a' ∈ L) (h : θ a * (θ a')⁻¹ ∈ J) : a⁻¹ * a' ∈ J := by
  have hl : a'⁻¹ * a ∈ L := L.mul_mem (L.inv_mem ha') ha
  have e : θ (a'⁻¹ * a) = θ a * (θ a')⁻¹ := by
    rw [hm _ (L.inv_mem ha') _ ha, theta_inv hm ha']
  have := hK (θ (a'⁻¹ * a)) ⟨e ▸ h, hL _ hl⟩
  rw [hi _ hl] at this
  simpa using J.inv_mem this

include hdc in
theorem InDC.theta {x g : G} (h : InDC J x g) (hg : g ∈ L) : InDC J x (θ g) := by
  obtain ⟨a, ha, b, hb, e⟩ := hdc g hg
  rw [e]
  exact h.mul ha.1 hb.1

include hm hi hK hL hdc in
theorem card_le_inv {x : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x⁻¹ A') (hAL : ∀ a ∈ A, a ∈ L) :
    A.card ≤ A'.card := by
  classical
  have := card_filter_le hA hA' (fun _ => True) (fun _ => True) (fun a => (θ a)⁻¹)
    (fun a ha _ => (InDC.theta hdc (hA.1 a ha) (hAL a ha)).inv) (fun _ _ _ _ _ => trivial)
    (fun a ha a' ha' h => theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa using h))
  simpa using this

open Classical in
include hm hi hK hL hdc in
theorem card_conv_le {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    {z : G} (hz : z ∈ L) :
    (A.filter fun a => InDC J y (a⁻¹ * z)).card ≤ (B.filter fun b => InDC J x (b⁻¹ * z)).card := by
  obtain ⟨k, hk, k', hk', e⟩ := hdc z hz
  refine card_filter_le hA hB _ _ (fun a => z * k' * (θ a)⁻¹) ?_ ?_ ?_
  · intro a ha hP
    have hl := L.inv_mem (hAL a ha)
    have h1 := InDC.theta hdc hP (L.mul_mem hl hz)
    rw [hm _ hl _ hz, theta_inv hm (hAL a ha), e] at h1
    simpa [mul_assoc] using h1.mul (J.inv_mem hk.1) J.one_mem
  · intro a ha _ c hc
    have h1 := InDC.theta hdc (hA.1 a ha) (hAL a ha)
    simpa [mul_assoc] using h1.mul (J.inv_mem hc) (J.inv_mem hk'.1)
  · intro a ha a' ha' h
    exact theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa [mul_assoc] using h)

end Theta

open Classical in

theorem card_pairs {J L : Subgroup G} {y : G} {A B : Finset G} (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    (hBL : ∀ b ∈ B, b ∈ L) {z : G} (hz : z ∈ L) :
    ((A ×ˢ B).filter fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))).card =
      (A.filter fun a => InDC J y (a⁻¹ * z)).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp ⊢
    refine ⟨hp.1.1, ?_⟩
    have h1 : InDC J y b := hB.1 b hp.1.2
    simpa [mul_assoc] using h1.mul J.one_mem (J.inv_mem hp.2.1)
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' e
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp hp' e
    subst e
    have h4 : b⁻¹ * b' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hp.2.1) hp'.2.1
    have := (hB.2 b' (hB.1 b' hp'.1.2)).unique ⟨hp.1.2, h4⟩ ⟨hp'.1.2, by simp⟩
    rw [this]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨b, ⟨hb, hj⟩, -⟩ := hB.2 _ ha.2
    refine ⟨(a, b), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨ha.1, hb⟩, ?_, L.mul_mem (L.inv_mem hz) (L.mul_mem (hAL a ha.1) (hBL b hb))⟩
    simpa [mul_assoc] using J.inv_mem hj

theorem dcOp_comm_and_card : ∀ {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J L : Subgroup G) (χ : J →* ℂˣ) (x y : G) (A B A' : Finset G) (F : G → W), (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ B, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J y B → IsDC J x⁻¹ A' → (∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) → dcOp A (dcOp B F) = dcOp B (dcOp A F) ∧ A.card = A'.card := by
  classical
  intro G W _ _ _ J L χ x y A B A' F _ hχ ⟨θ, hL, hm, hi, hK, hdc⟩ hAL hBL hAL' hA hB hA' hF
  refine ⟨?_, le_antisymm (card_le_inv hm hi hK hL hdc hA hA' hAL)
    (card_le_inv hm hi hK hL hdc hA' (by rwa [inv_inv]) hAL')⟩
  have hFK : ∀ g g' : G, (g : G ⧸ (J ⊓ L)) = g' → ∀ h, F (h * g) = F (h * g') := by
    intro g g' e h
    rw [QuotientGroup.eq] at e
    have := hF ⟨_, e.1⟩ (h * g)
    rw [hχ ⟨_, e.1⟩ e.2] at this
    simpa [mul_assoc] using this.symm
  have hms : (A ×ˢ B).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) =
      (B ×ˢ A).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [Multiset.count_map, Multiset.count_map]
      by_cases hz : z ∈ L
      · have e1 := card_pairs (A := A) hB hAL hBL hz
        have e2 := card_pairs (A := B) hA hBL hAL hz
        have e3 := le_antisymm (card_conv_le hm hi hK hL hdc hA hB hAL hz)
          (card_conv_le hm hi hK hL hdc hB hA hBL hz)
        have := e1.trans (e3.trans e2.symm)
        rw [Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val] at this
        convert this
      · have hz' : ∀ C D : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ D, a ∈ L) →
            Multiset.filter (fun p : G × G => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) (C ×ˢ D).val = 0 := by
          intro C D hC hD
          rw [Multiset.filter_eq_nil]
          intro p hp e
          rw [Finset.mem_val, Finset.mem_product] at hp
          rw [QuotientGroup.eq] at e
          apply hz
          simpa [mul_assoc] using L.mul_mem (L.mul_mem (hC _ hp.1) (hD _ hp.2)) (L.inv_mem e.2)
        rw [hz' A B hAL hBL, hz' B A hBL hAL]
  funext h
  have key : ∀ C D : Finset G, dcOp C (dcOp D F) h =
      (((C ×ˢ D).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L)))).map fun q => F (h * q.out)).sum := by
    intro C D
    rw [Multiset.map_map]
    change _ = ∑ p ∈ C ×ˢ D, _
    rw [Finset.sum_product]
    simp only [dcOp, Function.comp]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc]
    exact hFK _ _ (QuotientGroup.out_eq' _).symm h
  rw [key, key, hms]

end GlobalTheory.DoubleCosetComm
