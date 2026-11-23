import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu

namespace GlobalTheory.CompanionTheory.SegLayers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_injective (Δ : Segment k) : Function.Injective Δ.term := fun a b h =>
  Fin.ext ((IrrGL.nu_natCast_inj (x := Δ.first) Δ.d_pos).1 h)

theorem ms_nodup (Δ : Segment k) : Δ.ms.Nodup :=
  Multiset.Nodup.map (term_injective Δ) Finset.univ.nodup

theorem ncard_carrier (Δ : Segment k) : Δ.carrier.ncard = Δ.len := by
  rw [Segment.carrier, ← Set.image_univ, Set.ncard_image_of_injective _ (term_injective Δ)]
  simp

theorem ms_le {Δ : Segment k} {s : Multiset (IrrGL k)} (h : ∀ x ∈ Δ.carrier, x ∈ s) : Δ.ms ≤ s :=
  (Multiset.le_iff_subset (ms_nodup Δ)).2 fun _ hx => h _ (Segment.mem_ms.1 hx)

theorem exists_longest {s : Multiset (IrrGL k)} {y : IrrGL k} (hy : y ∈ s) (hc : y.IsCusp) :
    ∃ Γ : Segment k, (∀ x ∈ Γ.carrier, x ∈ s) ∧
      ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len := by
  classical
  let P : ℕ → Prop := fun l => ∃ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) ∧ D.len = l
  have hb : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Multiset.card s := fun D hD => by
    rw [← Segment.card_ms]
    exact Multiset.card_le_card (ms_le hD)
  have h1 : P 1 := ⟨Segment.single y hc, fun x hx => by
    rw [Segment.carrier_single] at hx
    exact hx ▸ hy, rfl⟩
  have h1' : 1 ≤ Multiset.card s := by
    obtain ⟨D, hD, e⟩ := h1
    exact e ▸ hb D hD
  obtain ⟨Γ, hΓ, e⟩ := Nat.findGreatest_spec h1' h1
  exact ⟨Γ, hΓ, fun D hD => e ▸ Nat.le_findGreatest (hb D hD) ⟨D, hD, rfl⟩⟩

theorem not_linked_of_longest {s : Multiset (IrrGL k)} {Γ D : Segment k} (hΓ : ∀ x ∈ Γ.carrier, x ∈ s)
    (hm : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len) (hD : ∀ x ∈ D.carrier, x ∈ s) :
    ¬ Γ.Linked D := by
  rintro ⟨⟨U, hU⟩, -, h2⟩
  have h3 : U.len ≤ Γ.len := hm U fun x hx => by
    rw [hU] at hx
    exact hx.elim (hΓ x) (hD x)
  have h4 : Γ.carrier ⊂ U.carrier := by
    rw [hU]
    exact ⟨Set.subset_union_left, fun h => h2 (Set.subset_union_right.trans h)⟩
  have h5 := Set.ncard_lt_ncard h4 (Set.finite_range U.term)
  rw [ncard_carrier, ncard_carrier] at h5
  omega

theorem exists_unlinked (n : ℕ) : ∀ s : Multiset (IrrGL k), Multiset.card s = n → (∀ y ∈ s, y.IsCusp) →
    ∃ m : Multiset (Segment k), (∀ D ∈ m, ∀ D' ∈ m, ¬ D.Linked D') ∧ m.bind Segment.ms = s := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    rcases Multiset.empty_or_exists_mem s with rfl | ⟨y, hy⟩
    · exact ⟨0, by simp, by simp⟩
    obtain ⟨Γ, hΓ, hm⟩ := exists_longest hy (hs y hy)
    have hle := ms_le hΓ
    have hsub : ∀ x ∈ s - Γ.ms, x ∈ s := fun x hx => Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    have hcard : Multiset.card (s - Γ.ms) < n := by
      have h1 := Multiset.card_sub hle
      have h2 := Multiset.card_le_card hle
      have h3 := Γ.len_pos
      rw [Segment.card_ms] at h1 h2
      omega
    obtain ⟨m, hu, hb⟩ := ih _ hcard _ rfl fun x hx => hs x (hsub x hx)
    have hin : ∀ D ∈ m, ∀ x ∈ D.carrier, x ∈ s := fun D hD x hx =>
      hsub x (hb ▸ Multiset.mem_bind.2 ⟨D, hD, Segment.mem_ms.2 hx⟩)
    have hΓD : ∀ D ∈ m, ¬ Γ.Linked D := fun D hD => not_linked_of_longest hΓ hm (hin D hD)
    refine ⟨Γ ::ₘ m, fun D hD D' hD' => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hD with e | e₁ <;> rcases Multiset.mem_cons.1 hD' with e' | e₂
      · rw [e, e']
        exact Segment.not_linked_self _
      · rw [e]
        exact hΓD _ e₂
      · rw [e']
        exact fun h => hΓD _ e₁ h.symm
      · exact hu _ e₁ _ e₂
    · rw [Multiset.cons_bind, hb]
      exact add_tsub_cancel_of_le hle

theorem unlinkedLayers (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    UnlinkedLayers k := by
  intro s hs
  obtain ⟨m, hu, hb⟩ := exists_unlinked _ s rfl hs
  have hmem : ∀ i : Fin m.toList.length, m.toList.get i ∈ m := fun i =>
    Multiset.mem_toList.1 (List.get_mem _ _)
  refine ⟨m.toList.length, m.toList.get, fun i j _ => hu _ (hmem i) _ (hmem j), ?_⟩
  have h1 : (Finset.univ.val.map m.toList.get : Multiset (Segment k)) = m := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  conv_rhs => rw [← hb, ← h1]
  simp [Multiset.bind, Multiset.map_map, Function.comp_def]

end GlobalTheory.CompanionTheory.SegLayers

end
