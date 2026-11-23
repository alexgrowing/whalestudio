import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IsIrreducibleIff

open UpperTheory.V.AlgebraTools

private theorem graph_equiv {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (A B W : Submodule k V) (hA : IsCompl A W) (hB : IsCompl B W) :
    ∃ e : A ≃ₗ[k] B, ∀ v : A, (v : V) - e v ∈ W := by
  have key : ∀ x : V, x - (B.projectionOnto W hB x : V) ∈ W := by
    intro x
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hB, map_sub,
      Submodule.projectionOnto_apply_left, sub_self]
  refine ⟨LinearEquiv.ofBijective ((B.projectionOnto W hB) ∘ₗ A.subtype) ⟨?_, ?_⟩, fun v => key v⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : (a : V) ∈ W := (Submodule.projectionOnto_apply_eq_zero_iff hB).1 ha
    exact Subtype.ext (Submodule.disjoint_def.1 hA.disjoint _ a.2 h1)
  · intro b
    have hb : (b : V) ∈ A ⊔ W := by rw [hA.sup_eq_top]; trivial
    obtain ⟨a, ha, w, hw, hsum⟩ := Submodule.mem_sup.1 hb
    refine ⟨⟨a, ha⟩, ?_⟩
    have h1 : a = (b : V) - w := by rw [← hsum]; abel
    have h2 : B.projectionOnto W hB w = 0 := (Submodule.projectionOnto_apply_eq_zero_iff hB).2 hw
    show B.projectionOnto W hB a = b
    rw [h1, map_sub, h2, sub_zero, Submodule.projectionOnto_apply_left]

theorem UpperTheory.V.AlgebraTools.mackeyTwo :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V) (H : Subgroup G) (s : G) (V₁ : Submodule k V), H.index = 2 → s ∉ H → StableOn ρ H V₁ → (∀ W ≤ V₁, StableOn ρ H W → W = ⊥ ∨ W = V₁) → IsCompl V₁ (V₁.map (ρ s)) → (¬ ∃ e : V₁ ≃ₗ[k] V₁.map (ρ s), ∀ h ∈ H, ∀ v w : V₁, (w : V) = ρ h v → (e w : V) = ρ h (e v)) → IrrOn ρ ⊤ := by
  intro k G V _ _ _ _ ρ H s V₁ hi hs hst hirr hc hne W hW
  have hmul : ∀ (a b : G) (x : V), ρ a (ρ b x) = ρ (a * b) x := by
    intro a b x; rw [map_mul]; rfl
  have hinv : ∀ x : V, ρ s⁻¹ (ρ s x) = x := by
    intro x; rw [hmul, inv_mul_cancel, map_one]; rfl
  have hinv' : ∀ x : V, ρ s (ρ s⁻¹ x) = x := by
    intro x; rw [hmul, mul_inv_cancel, map_one]; rfl
  have hconj : ∀ h ∈ H, s⁻¹ * (h * s) ∈ H := by
    intro h hh
    simp [Subgroup.mul_mem_iff_of_index_two hi, hs, hh]
  have hss : s * s ∈ H := by simp [Subgroup.mul_mem_iff_of_index_two hi]
  have hst2 : StableOn ρ H (V₁.map (ρ s)) := by
    rintro h hh _ ⟨v, hv, rfl⟩
    refine ⟨ρ (s⁻¹ * (h * s)) v, hst _ (hconj h hh) v hv, ?_⟩
    rw [hmul, hmul, mul_inv_cancel_left]
  have hW' : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g => hW g trivial
  rcases hirr (V₁ ⊓ W) inf_le_left
      (fun h hh v hv => ⟨hst h hh v hv.1, hW' h v hv.2⟩) with h0 | h1
  swap
  · right
    have hle : V₁ ≤ W := inf_eq_left.1 h1
    rw [eq_top_iff, ← hc.sup_eq_top]
    refine sup_le hle ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hW' s v (hle hv)
  have d1 : Disjoint V₁ W := disjoint_iff.2 h0
  have d2 : Disjoint (V₁.map (ρ s)) W := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨v, hv, rfl⟩ hw
    have : v ∈ W := hinv v ▸ hW' s⁻¹ _ hw
    rw [Submodule.disjoint_def.1 d1 v hv this, map_zero]
  rcases hirr (V₁ ⊓ (V₁.map (ρ s) ⊔ W)) inf_le_left (fun h hh v hv => ⟨hst h hh v hv.1, by
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hv.2
      rw [map_add]
      exact Submodule.add_mem_sup (hst2 h hh a ha) (hW' h w hw)⟩) with h2 | h2
  · left
    rw [eq_bot_iff]
    intro w hw
    have hb : w ∈ V₁ ⊔ V₁.map (ρ s) := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hsum⟩ := Submodule.mem_sup.1 hb
    have ha' : a ∈ V₁ ⊓ (V₁.map (ρ s) ⊔ W) := by
      refine ⟨ha, ?_⟩
      have : a = -b + w := by rw [← hsum]; abel
      rw [this]
      exact Submodule.add_mem_sup (neg_mem hb) hw
    rw [h2, Submodule.mem_bot] at ha'
    rw [ha', zero_add] at hsum
    exact Submodule.disjoint_def.1 d2 w (hsum ▸ hb) hw
  exfalso
  have hle : V₁ ≤ V₁.map (ρ s) ⊔ W := inf_eq_left.1 h2
  have c2 : IsCompl (V₁.map (ρ s)) W := by
    refine ⟨d2, codisjoint_iff.2 ?_⟩
    rw [eq_top_iff, ← hc.sup_eq_top]
    exact sup_le hle le_sup_left
  have c1 : IsCompl V₁ W := by
    refine ⟨d1, codisjoint_iff.2 ?_⟩
    rw [eq_top_iff, ← hc.sup_eq_top]
    refine sup_le le_sup_left ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨_, ⟨a, ha, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 (hle hv)
    rw [map_add, hmul]
    exact Submodule.add_mem_sup (hst _ hss a ha) (hW' s w hw)
  obtain ⟨e, he⟩ := graph_equiv _ _ _ c1 c2
  refine hne ⟨e, fun h hh v w hvw => ?_⟩
  have m1 : (e w : V) - ρ h (e v) ∈ V₁.map (ρ s) := sub_mem (e w).2 (hst2 h hh _ (e v).2)
  have m2 : (e w : V) - ρ h (e v) ∈ W := by
    have : (e w : V) - ρ h (e v) = ρ h ((v : V) - e v) - ((w : V) - e w) := by
      rw [map_sub, ← hvw]; abel
    rw [this]
    exact sub_mem (hW' h _ (he v)) (he w)
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 d2 _ m1 m2)
