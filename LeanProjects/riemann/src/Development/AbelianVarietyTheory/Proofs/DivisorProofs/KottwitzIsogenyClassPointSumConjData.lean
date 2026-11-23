import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.PointSumConj

theorem exists_conj_iff {G : Type} [Group G] (K : Subgroup G) (a m : G) :
    (∃ k ∈ K, a * k * a⁻¹ = m) ↔ a⁻¹ * m * a ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : a⁻¹ * (a * k * a⁻¹) * a = k := by group
    rw [this]; exact hk
  · intro h
    exact ⟨a⁻¹ * m * a, h, by group⟩

theorem mem_stab {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) (z : Γ) :
    z ∈ stab ι₁ ι₂ K₁ K₂ x ↔ x.1⁻¹ * ι₁ z * x.1 ∈ K₁ ∧ x.2⁻¹ * ι₂ z * x.2 ∈ K₂ := by
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, exists_conj_iff]

theorem finsum_dc_translate {G : Type} [Group G] (H H' K : Subgroup G) (a : G)
    (hH : ∀ h ∈ H, a * h * a⁻¹ ∈ H') (hH' : ∀ h ∈ H', a⁻¹ * h * a ∈ H) (F F' : G → ℂ)
    (hF : ∀ h ∈ H, ∀ k ∈ K, ∀ x, F (h * x * k) = F x) (hF' : ∀ x, F' (a * x) = F x) :
    ∑ᶠ q : DoubleCoset.Quotient (H' : Set G) (K : Set G), F' (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G), F (Quotient.out q) := by
  have key : ∀ x, F' (Quotient.out (DoubleCoset.mk H' K (a * x))) = F x := by
    intro x
    obtain ⟨h', hh', k, hk, he⟩ := (DoubleCoset.eq H' K _ _).1
      (DoubleCoset.out_eq' H' K (DoubleCoset.mk H' K (a * x))).symm
    rw [he]
    have : h' * (a * x) * k = a * ((a⁻¹ * h' * a) * x * k) := by group
    rw [this, hF', hF _ (hH' _ hh') _ hk]
  refine (finsum_eq_of_bijective (fun q : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    DoubleCoset.mk H' K (a * Quotient.out q)) ⟨?_, ?_⟩ (fun q => (key _).symm)).symm
  · intro q₁ q₂ h
    obtain ⟨h', hh', k, hk, he⟩ := (DoubleCoset.eq H' K _ _).1 h
    rw [← DoubleCoset.out_eq' H K q₁, ← DoubleCoset.out_eq' H K q₂]
    refine (DoubleCoset.eq H K _ _).2 ⟨a⁻¹ * h' * a, hH' _ hh', k, hk, ?_⟩
    have : Quotient.out q₂ = a⁻¹ * (a * Quotient.out q₂) := by group
    rw [this, he]; group
  · intro q'
    refine ⟨DoubleCoset.mk H K (a⁻¹ * Quotient.out q'), ?_⟩
    obtain ⟨h, hh, k, hk, he⟩ := (DoubleCoset.eq H K _ _).1
      (DoubleCoset.out_eq' H K (DoubleCoset.mk H K (a⁻¹ * Quotient.out q'))).symm
    simp only
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' H' K q']
    exact (DoubleCoset.eq H' K _ _).2 ⟨(a * h * a⁻¹)⁻¹, H'.inv_mem (hH _ hh), k⁻¹, K.inv_mem hk, by group⟩

end GlobalTheory.PointSumConj

namespace GlobalTheory.PointSumConj

theorem conj_mem_iff {G : Type} [Group G] (K : Subgroup G) {k : G} (hk : k ∈ K) (m : G) :
    k⁻¹ * m * k ∈ K ↔ m ∈ K := by
  rw [Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk)]

theorem card_stab_translate {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (y : Γ) (x k : G₁ × G₂) (hk : k ∈ K₁.prod K₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ ((ι₁ y, ι₂ y) * x * k)) = Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
  rw [Subgroup.mem_prod] at hk
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj y).toEquiv fun z => ?_)).symm
  simp only [SetLike.mem_coe, mem_stab, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply,
    Prod.fst_mul, Prod.snd_mul, map_mul, map_inv]
  have e1 : (ι₁ y * x.1 * k.1)⁻¹ * (ι₁ y * ι₁ z * (ι₁ y)⁻¹) * (ι₁ y * x.1 * k.1) =
      k.1⁻¹ * (x.1⁻¹ * ι₁ z * x.1) * k.1 := by group
  have e2 : (ι₂ y * x.2 * k.2)⁻¹ * (ι₂ y * ι₂ z * (ι₂ y)⁻¹) * (ι₂ y * x.2 * k.2) =
      k.2⁻¹ * (x.2⁻¹ * ι₂ z * x.2) * k.2 := by group
  rw [e1, e2, conj_mem_iff K₁ hk.1, conj_mem_iff K₂ hk.2]

theorem stab_conj {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (g₁ : G₁) (g₂ : G₂) (x : G₁ × G₂) :
    stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) K₁ K₂
      ((g₁⁻¹, g₂⁻¹) * x) = stab ι₁ ι₂ K₁ K₂ x := by
  ext z
  simp only [mem_stab, Prod.fst_mul, Prod.snd_mul, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : (g₁⁻¹ * x.1)⁻¹ * (g₁⁻¹ * ι₁ z * g₁⁻¹⁻¹) * (g₁⁻¹ * x.1) = x.1⁻¹ * ι₁ z * x.1 := by group
  have e2 : (g₂⁻¹ * x.2)⁻¹ * (g₂⁻¹ * ι₂ z * g₂⁻¹⁻¹) * (g₂⁻¹ * x.2) = x.2⁻¹ * ι₂ z * x.2 := by group
  rw [e1, e2]

theorem pointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ G₁ G₂ _ _ _ ι₁ ι₂ θ K₁ K₂ γ g₁ δ g₂ f φ hf hφ hγ hδ
  unfold pointSum
  refine finsum_dc_translate (ι₁.prod ι₂).range
    (((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁).prod ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)).range
    (K₁.prod K₂) (g₁⁻¹, g₂⁻¹) ?_ ?_
    (fun x => ((Nat.card (stab ι₁ ι₂ K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * θ x.2)))
    (fun x => ((Nat.card (stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)
      K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * (g₁⁻¹ * γ * g₁) * x.1) * φ (x.2⁻¹ * (g₂⁻¹ * δ * θ g₂) * θ x.2))) ?_ ?_
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply]
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply] <;> group
  · rintro _ ⟨y, rfl⟩ k hk x
    have hk' := (Subgroup.mem_prod).1 hk
    simp only [MonoidHom.prod_apply] at *
    rw [card_stab_translate ι₁ ι₂ K₁ K₂ y x k hk]
    congr 2
    · have e : ((ι₁ y, ι₂ y) * x * k).1⁻¹ * γ * ((ι₁ y, ι₂ y) * x * k).1 =
          k.1⁻¹ * (x.1⁻¹ * ((ι₁ y)⁻¹ * γ * ι₁ y) * x.1) * k.1 := by simp only [Prod.fst_mul]; group
      have e' : (ι₁ y)⁻¹ * γ * ι₁ y = γ := by rw [mul_assoc, ← hγ y]; group
      rw [e, e', hf _ hk'.1]
    · have e : ((ι₁ y, ι₂ y) * x * k).2⁻¹ * δ * θ ((ι₁ y, ι₂ y) * x * k).2 =
          k.2⁻¹ * (x.2⁻¹ * ((ι₂ y)⁻¹ * δ * θ (ι₂ y)) * θ x.2) * θ k.2 := by
        simp only [Prod.snd_mul, map_mul]; group
      have e' : (ι₂ y)⁻¹ * δ * θ (ι₂ y) = δ := by rw [mul_assoc, ← hδ y]; group
      rw [e, e', hφ _ hk'.2]
  · intro x
    rw [stab_conj]
    congr 2
    · congr 1; simp only [Prod.fst_mul]; group
    · congr 1; simp only [Prod.snd_mul, map_mul, map_inv]; group

end GlobalTheory.PointSumConj
