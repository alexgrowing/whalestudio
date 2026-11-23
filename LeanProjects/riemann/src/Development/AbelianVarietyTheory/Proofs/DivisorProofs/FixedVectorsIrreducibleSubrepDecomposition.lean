import Mathlib

open Submodule

namespace GlobalTheory.AbsDec

theorem exists_proj {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (ht : iSupIndep t) :
    ∃ T : ι → V →ₗ[ℂ] V, (∀ i v, T i v ∈ t i) ∧
      (∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (⨆ i, t i)
  have hcompl : ∀ i, IsCompl (t i) ((⨆ (j) (_ : j ≠ i), t j) ⊔ C) := by
    intro i
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨q, hq, c, hc, rfl⟩ := Submodule.mem_sup.1 hx'
      have hcQ : c ∈ ⨆ i, t i := by
        have h1 : q + c ∈ ⨆ i, t i := Submodule.mem_iSup_of_mem i hx
        have h2 : q ∈ ⨆ i, t i :=
          (iSup₂_le fun j _ => le_iSup t j : (⨆ (j) (_ : j ≠ i), t j) ≤ ⨆ i, t i) hq
        simpa using Submodule.sub_mem _ h1 h2
      have hc0 : c = 0 := (Submodule.disjoint_def.1 hC.disjoint) c hcQ hc
      subst hc0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.1 ((iSupIndep_def.1 ht) i)) q hx hq
    · rw [codisjoint_iff, eq_top_iff, ← hC.sup_eq_top]
      refine sup_le (iSup_le fun j => ?_) (le_sup_of_le_right le_sup_right)
      by_cases h : j = i
      · subst h; exact le_sup_left
      · exact le_sup_of_le_right (le_sup_of_le_left (le_iSup₂_of_le j h le_rfl))
  refine ⟨fun i => (t i).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ (hcompl i),
    fun i v => ?_, fun i j v hv => ?_⟩
  · simp
  · split_ifs with h
    · subst h
      exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hcompl i) ⟨v, hv⟩)
    · have hv' : v ∈ (⨆ (k) (_ : k ≠ i), t k) ⊔ C :=
        Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Ne.symm h) hv))
      have := Submodule.linearProjOfIsCompl_apply_right (hcompl i) ⟨v, hv'⟩
      exact congrArg Subtype.val this

theorem sum_proj {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) {v : V} (hv : v ∈ ⨆ i, t i) :
    ∑ i, T i v = v := by
  refine Submodule.iSup_induction t (motive := fun v => ∑ i, T i v = v) hv
    (fun j x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · simp [hT _ j x hx]
  · simp only [map_add, Finset.sum_add_distrib, hx, hy]

theorem proj_comm {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0)
    (hst : ∀ j g, ∀ v ∈ t j, ρ g v ∈ t j) (i : ι) (g : G) {v : V} (hv : v ∈ ⨆ j, t j) :
    T i (ρ g v) = ρ g (T i v) := by
  refine Submodule.iSup_induction t (motive := fun v => T i (ρ g v) = ρ g (T i v)) hv
    (fun j x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · rw [hT i j _ (hst j g x hx), hT i j x hx]
    split_ifs <;> simp
  · simp only [map_add, hx, hy]

end GlobalTheory.AbsDec

namespace GlobalTheory.AbsDec

theorem fixed_decomposition : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Set G) (F : Submodule ℂ V), (∀ v, v ∈ F ↔ ∀ k ∈ K, ρ k v = v) → ∀ 𝒜 : Set (Submodule ℂ V), (∀ P ∈ 𝒜, P ≠ ⊥ ∧ (∀ g, ∀ v ∈ P, ρ g v ∈ P) ∧ ∀ W : Submodule ℂ V, W ≤ P → (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = P) → FiniteDimensional ℂ ((⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V)) → ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ V), (∀ i, π i ∈ 𝒜 ∧ π i ⊓ F ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ F) ∧ (⨆ i, π i ⊓ F) = (⨆ P ∈ 𝒜, P ⊓ F) ∧ ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → ∃ i, ∃ T : V →ₗ[ℂ] V, (∀ v ∈ P, T v ∈ π i) ∧ (∀ v ∈ P, T v = 0 → v = 0) ∧ ∀ g, ∀ v ∈ P, T (ρ g v) = ρ g (T v) := by
  intro G V _ _ _ ρ K F hF 𝒜 h𝒜 hfd
  classical
  let good : Finset (Submodule ℂ V) → Prop := fun s =>
    (∀ P ∈ s, P ∈ 𝒜 ∧ P ⊓ F ≠ ⊥) ∧ s.SupIndep id
  have bound : ∀ s, good s → s.card ≤ Module.finrank ℂ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V) := by
    intro s hs
    have hv : ∀ P : s, ∃ v, v ∈ (P : Submodule ℂ V) ⊓ F ∧ v ≠ 0 := fun P =>
      Submodule.exists_mem_ne_zero_of_ne_bot (hs.1 P P.2).2
    choose v hv0 hvne using hv
    have hind : iSupIndep (fun P : s => (P : Submodule ℂ V) ⊓ F) :=
      ((iSupIndep_comp_coe_iff_supIndep (f := id)).2 hs.2).mono fun P => inf_le_left
    have hli : LinearIndependent ℂ v := hind.linearIndependent _ hv0 hvne
    have hvM : ∀ P : s, v P ∈ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V) := fun P =>
      (le_iSup₂_of_le (f := fun (Q : Submodule ℂ V) (_ : Q ∈ 𝒜) => Q ⊓ F)
        (P : Submodule ℂ V) (hs.1 P P.2).1 le_rfl) (hv0 P)
    have hli' : LinearIndependent ℂ
        (fun P : s => (⟨v P, hvM P⟩ : (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V))) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    simpa using hli'.fintype_card_le_finrank
  have h0 : ∃ s, good s ∧ s.card = 0 := ⟨∅, ⟨by simp, Finset.supIndep_empty _⟩, rfl⟩
  obtain ⟨s, hs, hsN⟩ := Nat.findGreatest_spec (P := fun n => ∃ s, good s ∧ s.card = n)
    (Nat.zero_le (Module.finrank ℂ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V))) h0
  have hmax : ∀ s', good s' → s'.card ≤ s.card := by
    intro s' hs'
    rw [hsN]
    by_contra hlt
    push_neg at hlt
    exact Nat.findGreatest_is_greatest hlt (bound s' hs') ⟨s', hs', rfl⟩
  have hQ : ∀ g, ∀ v ∈ ⨆ P : s, (P : Submodule ℂ V), ρ g v ∈ ⨆ P : s, (P : Submodule ℂ V) := by
    intro g v hv
    have : (⨆ P : s, (P : Submodule ℂ V)) ≤ (⨆ P : s, (P : Submodule ℂ V)).comap (ρ g) :=
      iSup_le fun P w hw => Submodule.mem_iSup_of_mem P ((h𝒜 P (hs.1 P P.2).1).2.1 g w hw)
    exact this hv
  have hsup : s.sup id = ⨆ P : s, (P : Submodule ℂ V) := by
    rw [Finset.sup_eq_iSup, iSup_subtype']
    rfl
  have hcover : ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → P ≤ ⨆ Q : s, (Q : Submodule ℂ V) := by
    intro P hP hPF
    obtain ⟨hne, hst, hirr⟩ := h𝒜 P hP
    rcases hirr (P ⊓ ⨆ Q : s, (Q : Submodule ℂ V)) inf_le_left
      (fun g v hv => ⟨hst g v hv.1, hQ g v hv.2⟩) with h | h
    · exfalso
      have hPs : P ∉ s := by
        intro hPs
        have hle : P ≤ P ⊓ ⨆ Q : s, (Q : Submodule ℂ V) :=
          le_inf le_rfl (le_iSup_of_le (⟨P, hPs⟩ : s) le_rfl)
        rw [h] at hle
        exact hne (eq_bot_iff.2 hle)
      have hgood : good (insert P s) := by
        refine ⟨fun R hR => ?_, hs.2.insert ?_⟩
        · rcases Finset.mem_insert.1 hR with rfl | hR
          · exact ⟨hP, hPF⟩
          · exact hs.1 R hR
        · rw [hsup, disjoint_iff]
          exact h
      have := hmax _ hgood
      rw [Finset.card_insert_of_notMem hPs] at this
      omega
    · rw [← h]
      exact inf_le_right
  have hind : iSupIndep (fun P : s => (P : Submodule ℂ V)) :=
    (iSupIndep_comp_coe_iff_supIndep (f := id)).2 hs.2
  obtain ⟨T, hTmem, hT⟩ := exists_proj (fun P : s => (P : Submodule ℂ V)) hind
  have hst' : ∀ (j : s) g, ∀ v ∈ (j : Submodule ℂ V), ρ g v ∈ (j : Submodule ℂ V) :=
    fun j => (h𝒜 j (hs.1 j j.2).1).2.1
  refine ⟨s, inferInstance, fun P => P, fun i => hs.1 i i.2, hind.mono fun i => inf_le_left,
    ?_, ?_⟩
  · apply le_antisymm
    · exact iSup_le fun i => le_iSup₂_of_le (f := fun (Q : Submodule ℂ V) (_ : Q ∈ 𝒜) => Q ⊓ F)
        (i : Submodule ℂ V) (hs.1 i i.2).1 le_rfl
    · refine iSup₂_le fun P hP => ?_
      by_cases hPF : P ⊓ F = ⊥
      · rw [hPF]
        exact bot_le
      intro φ hφ
      have hφQ := hcover P hP hPF hφ.1
      rw [← sum_proj _ T hT hφQ]
      refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨hTmem i φ, ?_⟩
      refine (hF _).2 fun k hk => ?_
      rw [← proj_comm ρ _ T hT hst' i k hφQ, (hF φ).1 hφ.2 k hk]
  · intro P hP hPF
    obtain ⟨hne, hst, hirr⟩ := h𝒜 P hP
    have hPQ := hcover P hP hPF
    have hex : ∃ i, ∀ v ∈ P, T i v = 0 → v = 0 := by
      by_contra hcon
      push_neg at hcon
      have hall : ∀ i, ∀ v ∈ P, T i v = 0 := by
        intro i
        obtain ⟨w, hwP, hw0, hwne⟩ := hcon i
        rcases hirr (P ⊓ LinearMap.ker (T i)) inf_le_left (fun g v hv => ⟨hst g v hv.1,
            LinearMap.mem_ker.2 (by
              rw [proj_comm ρ _ T hT hst' i g (hPQ hv.1), LinearMap.mem_ker.1 hv.2, map_zero])⟩)
          with h | h
        · exact absurd ((Submodule.eq_bot_iff _).1 h w ⟨hwP, hw0⟩) hwne
        · intro v hv
          have hv' : v ∈ P ⊓ LinearMap.ker (T i) := by rw [h]; exact hv
          exact hv'.2
      obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      apply hvne
      rw [← sum_proj _ T hT (hPQ hv)]
      exact Finset.sum_eq_zero fun i _ => hall i v hv
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, T i, fun v _ => hTmem i v, hi, fun g v hv => proj_comm ρ _ T hT hst' i g (hPQ hv)⟩

end GlobalTheory.AbsDec
