import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MassTor

section Closed

variable {G : Type} [Group G] [TopologicalSpace G]

theorem isCompact_closure_zpowers_iff {T : Subgroup G} (hT : IsClosed (T : Set G)) (t : T) :
    IsCompact (closure (Subgroup.zpowers (t : G) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set T)) := by
  have hE : Topology.IsClosedEmbedding (Subtype.val : T → G) := hT.isClosedEmbedding_subtypeVal
  have h1 : (Subgroup.zpowers (t : G) : Set G) = Subtype.val '' (Subgroup.zpowers t : Set T) := by
    have := MonoidHom.map_zpowers T.subtype t
    rw [← Subgroup.coe_subtype, ← Subgroup.coe_map, this]
  rw [h1, hE.closure_image_eq, ← hE.isEmbedding.isCompact_iff]

theorem cptPart_eq_map {T : Subgroup G} (hT : IsClosed (T : Set G)) :
    cptPart T = (Subgroup.closure {t : T | IsCompact (closure (Subgroup.zpowers t : Set T))}).map T.subtype := by
  rw [MonoidHom.map_closure]
  unfold cptPart
  congr 1
  ext g
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, (isCompact_closure_zpowers_iff hT ⟨g, hg⟩).1 hc, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2, (isCompact_closure_zpowers_iff hT t).2 ht⟩

theorem cptPart_le (T : Subgroup G) : cptPart T ≤ T :=
  (Subgroup.closure_le _).2 fun _ hg => hg.1

theorem mem_cptPart_iff {T : Subgroup G} (hT : IsClosed (T : Set G)) (t : T) :
    (t : G) ∈ cptPart T ↔ t ∈ Subgroup.closure {s : T | IsCompact (closure (Subgroup.zpowers s : Set T))} := by
  rw [cptPart_eq_map hT, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, h⟩
    rwa [show s = t from Subtype.ext h] at hs
  · intro h
    exact ⟨t, h, rfl⟩

end Closed

theorem mem_closure_cpt_iff {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] (e : A ≃ₜ* B)
    (a : A) :
    a ∈ Subgroup.closure {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))} ↔
      e a ∈ Subgroup.closure {s : B | IsCompact (closure (Subgroup.zpowers s : Set B))} := by
  have key : ∀ s : A, IsCompact (closure (Subgroup.zpowers s : Set A)) ↔
      IsCompact (closure (Subgroup.zpowers (e s) : Set B)) := by
    intro s
    have h1 : (Subgroup.zpowers (e s) : Set B) = e '' (Subgroup.zpowers s : Set A) := by
      have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom s
      have h := congrArg (fun H : Subgroup B => (H : Set B)) this
      rw [Subgroup.coe_map] at h
      exact h.symm
    rw [h1]
    have h2 := e.toHomeomorph.image_closure (Subgroup.zpowers s : Set A)
    have h3 := e.toHomeomorph.isCompact_image (s := closure (Subgroup.zpowers s : Set A))
    rw [show (⇑e.toHomeomorph : A → B) = ⇑e from rfl] at h2 h3
    rw [← h2, h3]
  have himg : e.toMulEquiv.toMonoidHom '' {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))} =
      {s : B | IsCompact (closure (Subgroup.zpowers s : Set B))} := by
    ext b
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (key s).1 hs
    · intro hb
      refine ⟨e.symm b, (key _).2 ?_, ?_⟩
      · simpa using hb
      · exact e.apply_symm_apply b
  have hmap := MonoidHom.map_closure e.toMulEquiv.toMonoidHom
    {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))}
  rw [himg] at hmap
  rw [← hmap, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    have : x = a := e.injective h
    rwa [← this]

theorem card_doubleCoset_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (H K : Subgroup A) (H' K' : Subgroup B)
    (hH : ∀ a, a ∈ H ↔ e a ∈ H') (hK : ∀ a, a ∈ K ↔ e a ∈ K') :
    Nat.card (DoubleCoset.Quotient (H : Set A) (K : Set A)) =
      Nat.card (DoubleCoset.Quotient (H' : Set B) (K' : Set B)) := by
  apply Nat.card_congr
  refine Quotient.congr e.toEquiv fun x y => ?_
  rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨e a, (hH a).1 ha, e b, (hK b).1 hb, by simp [map_mul]⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨e.symm a, (hH _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] at h
    simp [map_mul, h]

theorem isClosed_twCent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G)
    (hθ : Continuous θ) (δ : G) : IsClosed (twCent θ δ : Set G) :=
  isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)

theorem mass_eq_of_equiv (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G')
    (δ : G) (δ' : G') (hT : IsClosed (twCent θ δ : Set G)) (hT' : IsClosed (twCent θ' δ' : Set G'))
    (e : twCent θ δ ≃ₜ* twCent θ' δ')
    (hΓ : ∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') :
    mass θ Γ δ = mass θ' Γ' δ' := by
  have hC : ∀ t : twCent θ δ, (t : G) ∈ cptPart (twCent θ δ) ↔ ((e t : twCent θ' δ') : G') ∈ cptPart (twCent θ' δ') :=
    fun t => by rw [mem_cptPart_iff hT, mem_cptPart_iff hT', mem_closure_cpt_iff e]
  have hmem : ∀ t : twCent θ δ, (t : G) ∈ Γ ⊓ cptPart (twCent θ δ) ↔
      ((e t : twCent θ' δ') : G') ∈ Γ' ⊓ cptPart (twCent θ' δ') := fun t => by
    simp only [Subgroup.mem_inf]
    rw [hΓ t, hC t]
  let f : (Γ ⊓ cptPart (twCent θ δ) : Subgroup G) ≃ (Γ' ⊓ cptPart (twCent θ' δ') : Subgroup G') :=
    { toFun := fun g => ⟨(e ⟨g, cptPart_le _ g.2.2⟩ : G'), (hmem _).1 g.2⟩
      invFun := fun g' => ⟨(e.symm ⟨g', cptPart_le _ g'.2.2⟩ : G),
        (hmem (e.symm ⟨g', cptPart_le _ g'.2.2⟩)).2 (by rw [e.apply_symm_apply]; exact g'.2)⟩
      left_inv := fun g => by ext; simp
      right_inv := fun g' => by ext; simp }
  unfold mass
  rw [card_doubleCoset_congr e.toMulEquiv _ _ (Γ'.subgroupOf (twCent θ' δ')) ((cptPart (twCent θ' δ')).subgroupOf _)
    (fun a => by simp only [Subgroup.mem_subgroupOf]; exact hΓ a)
    (fun a => by simp only [Subgroup.mem_subgroupOf]; exact hC a), Nat.card_congr f]

end GlobalTheory.MassTor
