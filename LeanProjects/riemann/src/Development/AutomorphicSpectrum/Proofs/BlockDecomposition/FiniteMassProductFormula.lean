import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

noncomputable section

open GlobalTheory.BCT

namespace GlobalTheory.CompanionTheory.MassProd

section Cards

variable {A B C : Type} [Group A] [Group B] [Group C]

theorem card_doubleCoset (e : C ≃* A × B) (H K : Subgroup A) (H' K' : Subgroup B) (H'' K'' : Subgroup C)
    (hH : ∀ c, c ∈ H'' ↔ (e c).1 ∈ H ∧ (e c).2 ∈ H') (hK : ∀ c, c ∈ K'' ↔ (e c).1 ∈ K ∧ (e c).2 ∈ K') :
    Nat.card (DoubleCoset.Quotient (H'' : Set C) (K'' : Set C)) =
      Nat.card (DoubleCoset.Quotient (H : Set A) (K : Set A)) *
        Nat.card (DoubleCoset.Quotient (H' : Set B) (K' : Set B)) := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let F : C → DoubleCoset.Quotient (H : Set A) (K : Set A) × DoubleCoset.Quotient (H' : Set B) (K' : Set B) :=
    fun c => (DoubleCoset.mk H K (e c).1, DoubleCoset.mk H' K' (e c).2)
  have hF : ∀ x y : C, F x = F y ↔ DoubleCoset.mk H'' K'' x = DoubleCoset.mk H'' K'' y := by
    intro x y
    simp only [F, Prod.mk.injEq, DoubleCoset.eq]
    constructor
    · rintro ⟨⟨h, hh, k, hk, h1⟩, h', hh', k', hk', h2⟩
      refine ⟨e.symm (h, h'), ?_, e.symm (k, k'), ?_, ?_⟩
      · rw [hH]; simpa using ⟨hh, hh'⟩
      · rw [hK]; simpa using ⟨hk, hk'⟩
      · apply e.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact Prod.ext (by simpa using h1) (by simpa using h2)
    · rintro ⟨h, hh, k, hk, rfl⟩
      rw [hH] at hh
      rw [hK] at hk
      exact ⟨⟨_, hh.1, _, hk.1, by simp⟩, _, hh.2, _, hk.2, by simp⟩
  refine Equiv.ofBijective (Quotient.lift F fun x y h => (hF x y).2 (Quotient.sound h)) ⟨?_, ?_⟩
  · intro p q
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    intro h
    exact (hF x y).1 h
  · rintro ⟨p, q⟩
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    refine ⟨DoubleCoset.mk H'' K'' (e.symm (x, y)), ?_⟩
    show F (e.symm (x, y)) = _
    simp [F]

end Cards

section Top

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

theorem twCent_prodMap (θ : G →* G) (θ' : G' →* G') (δ : G) (δ' : G') :
    twCent (θ.prodMap θ') (δ, δ') = (twCent θ δ).prod (twCent θ' δ') := by
  ext ⟨a, b⟩
  show (a, b) * (δ, δ') = (δ, δ') * (θ a, θ' b) ↔ a * δ = δ * θ a ∧ b * δ' = δ' * θ' b
  simp [Prod.ext_iff]

theorem compactPowers_prod (a : G) (b : G') :
    IsCompact (closure (Subgroup.zpowers ((a, b) : G × G') : Set (G × G'))) ↔
      IsCompact (closure (Subgroup.zpowers a : Set G)) ∧ IsCompact (closure (Subgroup.zpowers b : Set G')) := by
  constructor
  · intro h
    constructor
    · refine (h.image continuous_fst).closure_of_subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(a, b) ^ n, subset_closure ⟨n, rfl⟩, by simp⟩
    · refine (h.image continuous_snd).closure_of_subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(a, b) ^ n, subset_closure ⟨n, rfl⟩, by simp⟩
  · rintro ⟨h, h'⟩
    refine (h.prod h').closure_of_subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨subset_closure ⟨n, by simp⟩, subset_closure ⟨n, by simp⟩⟩

theorem cptPart_prod (T : Subgroup G) (T' : Subgroup G') :
    cptPart (T.prod T') = (cptPart T).prod (cptPart T') := by
  have h1 : ∀ {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X],
      IsCompact (closure (Subgroup.zpowers (1 : X) : Set X)) := by
    intro X _ _ _
    simpa using (isCompact_singleton (x := (1 : X))).closure
  unfold cptPart
  have hs : (1 : G) ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := ⟨T.one_mem, h1⟩
  have hs' : (1 : G') ∈ {t | t ∈ T' ∧ IsCompact (closure (Subgroup.zpowers t : Set G'))} := ⟨T'.one_mem, h1⟩
  rw [← Subgroup.closure_prod hs hs']
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_prod, compactPowers_prod, Subgroup.mem_prod]
  tauto

theorem card_inf_prod (Γ C : Subgroup G) (Γ' C' : Subgroup G') :
    Nat.card (Γ.prod Γ' ⊓ C.prod C' : Subgroup (G × G')) =
      Nat.card (Γ ⊓ C : Subgroup G) * Nat.card (Γ' ⊓ C' : Subgroup G') := by
  have h : Γ.prod Γ' ⊓ C.prod C' = (Γ ⊓ C).prod (Γ' ⊓ C') := by
    ext ⟨a, b⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_prod]
    tauto
  rw [h, ← Nat.card_prod]
  exact Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv

end Top

theorem massProd : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  intro G G' _ _ _ _ _ _ θ θ' Γ Γ' δ δ'
  unfold mass
  rw [twCent_prodMap, cptPart_prod, card_inf_prod]
  rw [card_doubleCoset (Subgroup.prodEquiv (twCent θ δ) (twCent θ' δ'))
    (Γ.subgroupOf (twCent θ δ)) ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ))
    (Γ'.subgroupOf (twCent θ' δ')) ((cptPart (twCent θ' δ')).subgroupOf (twCent θ' δ'))
    _ _ (fun c => by simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod]; exact Iff.rfl)
    (fun c => by simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod]; exact Iff.rfl)]
  push_cast
  rw [mul_div_mul_comm]

end GlobalTheory.CompanionTheory.MassProd

end
