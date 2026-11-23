import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.BurnsideHom

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem count_step (l : ℕ) [hl : Fact l.Prime] (G : Type) [Group G] :
    ∀ (h : ℕ) (S : Subgroup (G →* Multiplicative (ZMod l))), Finite S → Nat.card S ≤ l ^ h →
      ∃ x : Fin h → G, ∀ f ∈ S, (∀ i, f (x i) = 1) → f = 1 := by
  intro h
  induction h with
  | zero =>
    intro S _ hS
    refine ⟨Fin.elim0, fun f hf _ => ?_⟩
    have hbot : S = ⊥ := Subgroup.eq_bot_of_card_le S (by simpa using hS)
    rw [hbot, Subgroup.mem_bot] at hf
    exact hf
  | succ h ih =>
    intro S hfin hS
    by_cases htriv : ∀ f ∈ S, f = 1
    · exact ⟨fun _ => 1, fun f hf _ => htriv f hf⟩
    push_neg at htriv
    obtain ⟨f₀, hf₀, hne⟩ := htriv
    obtain ⟨g, hg⟩ : ∃ g, f₀ g ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hne (MonoidHom.ext hc)
    let ev : S →* Multiplicative (ZMod l) :=
      { toFun := fun f => (f : G →* Multiplicative (ZMod l)) g
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hrange : Nat.card ev.range = l := by
      have hdvd : Nat.card ev.range ∣ l := by
        have := Subgroup.card_subgroup_dvd_card ev.range
        simpa [Nat.card_zmod] using this
      rcases (Nat.dvd_prime hl.out).mp hdvd with h1 | h1
      · exfalso
        have hbot : ev.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
        have hmem : ev ⟨f₀, hf₀⟩ ∈ ev.range := ⟨_, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hg hmem
      · exact h1
    have hcardS : Nat.card ev.ker * l = Nat.card S := by
      have := Subgroup.card_mul_index ev.ker
      rw [Subgroup.index_ker, hrange] at this
      exact this
    let S' : Subgroup (G →* Multiplicative (ZMod l)) := ev.ker.map S.subtype
    have hS' : Nat.card S' = Nat.card ev.ker := Subgroup.card_map_of_injective S.subtype_injective
    have hfin' : Finite S' := Nat.finite_of_card_ne_zero (by
      rw [hS']
      intro h0
      have : Nat.card S = 0 := by rw [← hcardS, h0, zero_mul]
      exact (Nat.card_pos (α := S)).ne' this)
    have hle : Nat.card S' ≤ l ^ h := by
      rw [hS']
      have hlpos : 0 < l := hl.out.pos
      have : Nat.card ev.ker * l ≤ l ^ h * l := by
        rw [hcardS, ← pow_succ]
        exact hS
      exact Nat.le_of_mul_le_mul_right this hlpos
    obtain ⟨x', hx'⟩ := ih S' hfin' hle
    refine ⟨Fin.cons g x', fun f hf hall => ?_⟩
    have hfg : f g = 1 := by simpa using hall 0
    have hmem : f ∈ S' := ⟨⟨f, hf⟩, hfg, rfl⟩
    exact hx' f hmem fun i => by simpa using hall i.succ

theorem UpperTheory.V.AlgebraTools.topGen_of_hom :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G], IsProL l G →
      (∀ s : Set G, (∀ f : G →* Multiplicative (ZMod l), IsOpen (f.ker : Set G) → (∀ g ∈ s, f g = 1) → f = 1) → TopGen s) ∧
      (∀ h : ℕ, {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.Finite →
        {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.ncard ≤ l ^ h → ∃ x : Fin h → G, TopGen (Set.range x)) := by
  intro l _ G _ _ _ _ _ hpro
  have partA : ∀ s : Set G, (∀ f : G →* Multiplicative (ZMod l), IsOpen (f.ker : Set G) →
      (∀ g ∈ s, f g = 1) → f = 1) → TopGen s := by
    intro s hs
    let H := (Subgroup.closure s).topologicalClosure
    have hHc : IsClosed (H : Set G) := Subgroup.isClosed_topologicalClosure _
    show Dense (Subgroup.closure s : Set G)
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro g
    by_contra hg
    have hg' : g ∉ (H : Set G) := by
      rw [Subgroup.topologicalClosure_coe]
      exact hg
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (U := (fun n => g * n) ⁻¹' (H : Set G)ᶜ)
      (hHc.isOpen_compl.preimage (continuous_const_mul g))
      (by simp only [Set.mem_preimage, Set.mem_compl_iff, mul_one]; exact hg')
    let Ns : Subgroup G := N.toOpenSubgroup
    haveI : Ns.Normal := N.isNormal'
    haveI : Finite (G ⧸ Ns) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
    let K := H.map (QuotientGroup.mk' Ns)
    have hK : K = ⊤ := by
      refine UpperTheory.V.CF.burnsideHom l (G ⧸ Ns) (hpro N) K (fun f hf => ?_)
      let F := f.comp (QuotientGroup.mk' Ns)
      have hFo : IsOpen (F.ker : Set G) := by
        refine Subgroup.isOpen_mono (H₁ := Ns) (fun x hx => ?_) N.isOpen'
        rw [MonoidHom.mem_ker]
        simp [F, (QuotientGroup.eq_one_iff x).mpr hx]
      have hF : F = 1 := hs F hFo (fun x hx => by
        have hxH : x ∈ H := Subgroup.le_topologicalClosure _ (Subgroup.subset_closure hx)
        exact hf ⟨x, hxH, rfl⟩)
      ext q
      simpa [F] using DFunLike.congr_fun hF q
    have hgK : (QuotientGroup.mk' Ns g) ∈ K := by
      rw [hK]
      exact Subgroup.mem_top _
    obtain ⟨y, hyH, hy⟩ := hgK
    have hyg : y⁻¹ * g ∈ Ns := QuotientGroup.eq.mp hy
    have hn : g⁻¹ * y ∈ Ns := by
      have := Ns.inv_mem hyg
      simpa using this
    have hU := hN hn
    simp only [Set.mem_preimage, Set.mem_compl_iff, mul_inv_cancel_left] at hU
    exact hU hyH
  refine ⟨partA, fun h hfin hcard => ?_⟩
  let S : Subgroup (G →* Multiplicative (ZMod l)) :=
    { carrier := {f | IsOpen (f.ker : Set G)}
      one_mem' := by
        show IsOpen ((1 : G →* Multiplicative (ZMod l)).ker : Set G)
        rw [MonoidHom.ker_one]
        exact isOpen_univ
      mul_mem' := fun {a b} ha hb => by
        show IsOpen ((a * b).ker : Set G)
        refine Subgroup.isOpen_mono (H₁ := a.ker ⊓ b.ker) (fun x hx => ?_) ?_
        · rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
          rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hx.1, hx.2, one_mul]
        · rw [Subgroup.coe_inf]
          exact IsOpen.inter ha hb
      inv_mem' := fun {a} ha => by
        show IsOpen ((a⁻¹).ker : Set G)
        have : (a⁻¹).ker = a.ker := by
          ext x
          simp [MonoidHom.mem_ker]
        rw [this]
        exact ha }
  haveI : Finite S := hfin.to_subtype
  have hle : Nat.card S ≤ l ^ h := by
    have : Nat.card S = {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.ncard :=
      Nat.card_coe_set_eq _
    rw [this]
    exact hcard
  obtain ⟨x, hx⟩ := count_step l G h S inferInstance hle
  exact ⟨x, partA _ fun f hf hv => hx f hf fun i => hv _ ⟨i, rfl⟩⟩
