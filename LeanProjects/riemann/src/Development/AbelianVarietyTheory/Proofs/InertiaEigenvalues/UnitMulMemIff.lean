import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerpEqPerpNb

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem step_exists (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField O)] {N : ℕ}
    {L Λ : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) (hΛ : Good cK J ϖ N Λ) (hne : L ≠ Λ)
    (hi : Λ.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    ∃ L' ∈ Nbrs cK J ϖ L, Good cK J ϖ N L' ∧ Λ.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0 ∧
      Nat.card (IsLocalRing.ResidueField O) * Λ.toAddSubgroup.relIndex L'.toAddSubgroup ≤
        Λ.toAddSubgroup.relIndex L.toAddSubgroup := by
  classical
  have hnle : ¬ Λ ≤ L := by
    intro hle
    apply hne
    refine le_antisymm (fun x hx => (hΛ.1 x).2 fun y hy => (hL.1 x).1 hx y (hle hy)) hle
  obtain ⟨x, hxΛ, hxL⟩ := Set.not_subset.1 hnle
  have hex : ∃ k : ℕ, (ϖ ^ k) • x ∈ L := hL.2.1 x
  set k0 := Nat.find hex with hk0
  have hk0m : (ϖ ^ k0) • x ∈ L := Nat.find_spec hex
  have hk0pos : k0 ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_smul] at hk0m
    exact hxL hk0m
  set v := (ϖ ^ (k0 - 1)) • x with hvdef
  have hvΛ : v ∈ Λ := Λ.smul_mem _ hxΛ
  have hvL : v ∉ L := Nat.find_min hex (by omega : k0 - 1 < k0)
  have hwL : ϖ • v ∈ L := by
    rw [hvdef, smul_smul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0pos)]
    exact hk0m
  have hvv := (hΛ.1 v).1 hvΛ v hvΛ
  have hstep : IsStep cK J ϖ L v := ⟨hvL, hwL, hvv⟩
  have hgood := good_nb c cK hcK hc2 hJ hϖ hL hstep
  refine ⟨nb cK J L v, ⟨v, hstep, rfl⟩, hgood, ?_⟩

  set Q := Nat.card (IsLocalRing.ResidueField O)
  have hQ := perp_relIndex c cK hcK hϖ hL.1 hvL hwL
  set Ag := Λ.toAddSubgroup
  set large₂ := L.toAddSubgroup
  set L'g := (nb cK J L v).toAddSubgroup
  set Mpg := (perp cK J L v).toAddSubgroup
  set Mg := large₂ ⊓ Ag
  set Ng := Mg ⊔ (Submodule.span O {v}).toAddSubgroup
  have hMMp : Mg ≤ Mpg := fun y hy => mem_perp.2 ⟨hy.1, (hΛ.1 v).1 hvΛ y hy.2⟩
  have hMpL : Mpg ≤ large₂ := fun y hy => (mem_perp.1 hy).1
  have hMN : Mg ≤ Ng := le_sup_left
  have hspanΛ : (Submodule.span O {v}).toAddSubgroup ≤ Ag := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact Λ.smul_mem a hvΛ
  have hNA : Ng ≤ Ag := sup_le (fun y hy => hy.2) hspanΛ
  have hL'eq : L'g = Mpg ⊔ Ng := by
    apply le_antisymm
    · intro y hy
      obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hy
      exact AddSubgroup.add_mem_sup hm
        (AddSubgroup.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, rfl⟩))
    · refine sup_le (fun y hy => mem_nb.2 ⟨y, hy, 0, by simp⟩) (sup_le ?_ ?_)
      · intro y hy
        exact mem_nb.2 ⟨y, hMMp hy, 0, by simp⟩
      · intro y hy
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        exact mem_nb.2 ⟨0, (perp cK J L v).zero_mem, a, by simp⟩
  have d1 : Ag.relIndex L'g ∣ Ng.relIndex L'g := AddSubgroup.relIndex_dvd_of_le_left (L := L'g) hNA
  have e1 : Ng.relIndex L'g = Ng.relIndex Mpg := by
    rw [hL'eq]; exact AddSubgroup.relIndex_sup_right (H := Mpg) (K := Ng)
  have d2 : Ng.relIndex Mpg ∣ Mg.relIndex Mpg := AddSubgroup.relIndex_dvd_of_le_left (L := Mpg) hMN
  have e2 : Ag.relIndex large₂ = Mg.relIndex Mpg * Q := by
    rw [← AddSubgroup.inf_relIndex_right, inf_comm, show Q = Mpg.relIndex large₂ from hQ.symm]
    exact (AddSubgroup.relIndex_mul_relIndex _ _ _ hMMp hMpL).symm
  rw [e1] at d1
  have d := dvd_trans d1 d2
  have hm0 : Mg.relIndex Mpg ≠ 0 := by
    intro h0; rw [e2, h0, zero_mul] at hi; exact hi rfl
  have ha0 : Ag.relIndex L'g ≠ 0 := by
    intro h0; rw [h0, zero_dvd_iff] at d; exact hm0 d
  refine ⟨ha0, ?_⟩
  rw [e2, mul_comm (Mg.relIndex Mpg)]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) d)

theorem unit_mul_mem_iff (u : Oˣ) (y : K) :
    algebraMap O K u * y ∈ (algebraMap O K).range ↔ y ∈ (algebraMap O K).range := by
  constructor
  · intro h
    have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul]; simp
    have : y = algebraMap O K ((u⁻¹ : Oˣ) : O) * (algebraMap O K u * y) := by
      rw [← mul_assoc, e1, one_mul]
    rw [this]; exact mul_mem ⟨_, rfl⟩ h
  · intro h; exact mul_mem ⟨_, rfl⟩ h

theorem perp_congr {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)}
    (hSD : IsSD cK J L) {v v0 : Fin r → K} (h : v - v0 ∈ L) :
    perp cK J L v = perp cK J L v0 := by
  ext x
  rw [mem_perp, mem_perp]
  constructor
  · rintro ⟨hx, h1⟩
    refine ⟨hx, ?_⟩
    have h2 := (hSD _).1 h x hx
    rw [hf_sub_left] at h2
    have := sub_mem h1 h2
    simpa using this
  · rintro ⟨hx, h1⟩
    refine ⟨hx, ?_⟩
    have h2 := (hSD _).1 h x hx
    rw [hf_sub_left] at h2
    have := add_mem h1 h2
    simpa using this

theorem nb_congr {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)}
    {v1 v2 : Fin r → K} (hp : perp cK J L v1 = perp cK J L v2) (h : v2 - v1 ∈ perp cK J L v1) :
    nb cK J L v1 = nb cK J L v2 := by
  ext x
  rw [mem_nb, mem_nb]
  constructor
  · rintro ⟨m, hm, a, rfl⟩
    refine ⟨m - a • (v2 - v1), hp ▸ sub_mem hm (Submodule.smul_mem _ a h), a, ?_⟩
    rw [smul_sub]; abel
  · rintro ⟨m, hm, a, rfl⟩
    refine ⟨m + a • (v2 - v1), add_mem (hp ▸ hm) (Submodule.smul_mem _ a h), a, ?_⟩
    rw [smul_sub]; abel

theorem isStep_unit_smul (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} {L : Submodule O (Fin r → K)} {v : Fin r → K}
    (hs : IsStep cK J ϖ L v) {b : O} (hb : IsUnit b) : IsStep cK J ϖ L (b • v) := by
  obtain ⟨hv, hw, hvv⟩ := hs
  refine ⟨fun h => hv ?_, ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := hb
    have := L.smul_mem ((u⁻¹ : Oˣ) : O) h
    rwa [smul_smul, Units.inv_mul, one_smul] at this
  · rw [smul_comm]; exact L.smul_mem b hw
  · rw [hf_algSmul_left, hf_algSmul_right, hcK]
    exact mul_mem ⟨_, rfl⟩ (mul_mem ⟨_, rfl⟩ hvv)

theorem nb_unit_smul (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)} {v : Fin r → K}
    {b : O} (hb : IsUnit b) : nb cK J L (b • v) = nb cK J L v := by
  have hp : perp cK J L (b • v) = perp cK J L v := by
    ext x
    rw [mem_perp, mem_perp, hf_algSmul_left, hcK]
    obtain ⟨u, hu⟩ := hb.map c
    rw [← hu, unit_mul_mem_iff]
  unfold nb
  rw [hp, Submodule.span_singleton_smul_eq hb]

theorem sub_mem_of_mk_eq {ϖ : O} (hϖ : Irreducible ϖ) {L : Submodule O (Fin r → K)}
    {v v0 : Fin r → K} (hw : ϖ • v ∈ L) (hw0 : ϖ • v0 ∈ L)
    (h : (QuotientAddGroup.mk (⟨ϖ • v, hw⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸
      (L.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf
        L.toAddSubgroup) = QuotientAddGroup.mk (⟨ϖ • v0, hw0⟩ : L.toAddSubgroup)) :
    v - v0 ∈ L := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨y, hy, hy'⟩ := h
  have e : ϖ • y = ϖ • (v0 - v) := by
    rw [smul_sub]
    simpa [neg_add_eq_sub] using hy'
  have := smul_injective (K := K) (r := r) hϖ e
  rw [show v - v0 = -(v0 - v) by abel, ← this]
  exact L.neg_mem hy

theorem card_nbrs (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField O)] {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) (hN : N ≠ 0)
    (t : Finset (Submodule O (Fin r → K))) (ht : (t : Set _) ⊆ Nbrs cK J ϖ L) :
    t.card * (Nat.card (IsLocalRing.ResidueField O) - 1) ≤
      N * Nat.card (IsLocalRing.ResidueField O) := by
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  set Wg := (L.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf
    L.toAddSubgroup with hWg
  have hcardW : Nat.card (L.toAddSubgroup ⧸ Wg) = N := hL.2.2
  haveI : Finite (L.toAddSubgroup ⧸ Wg) := Nat.finite_of_card_ne_zero (hcardW ▸ hN)
  letI := Fintype.ofFinite (L.toAddSubgroup ⧸ Wg)
  let rel : Submodule O (Fin r → K) → (L.toAddSubgroup ⧸ Wg) → Prop := fun L' u =>
    ∃ v, IsStep cK J ϖ L v ∧ L' = nb cK J L v ∧ ∃ hw : ϖ • v ∈ L,
      (QuotientAddGroup.mk (⟨ϖ • v, hw⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ Wg) = u
  choose lift hlift using IsLocalRing.residue_surjective (R := O)
  have hunit : ∀ a : (IsLocalRing.ResidueField O)ˣ, IsUnit (lift a) := by
    intro a
    by_contra h
    apply a.ne_zero
    rw [← hlift (a : IsLocalRing.ResidueField O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hm : ∀ L' ∈ t, Nat.card (IsLocalRing.ResidueField O) - 1 ≤
      (Finset.univ.filter (fun u => rel L' u)).card := by
    intro L' hL'
    obtain ⟨v, hs, rfl⟩ := ht hL'
    have hmem : ∀ a : (IsLocalRing.ResidueField O)ˣ, ϖ • (lift a • v) ∈ L := fun a => by
      rw [smul_comm]; exact L.smul_mem _ hs.2.1
    let f : (IsLocalRing.ResidueField O)ˣ → L.toAddSubgroup ⧸ Wg := fun a =>
      QuotientAddGroup.mk (⟨ϖ • (lift a • v), hmem a⟩ : L.toAddSubgroup)
    have hcu : Nat.card (IsLocalRing.ResidueField O) - 1 =
        (Finset.univ : Finset (IsLocalRing.ResidueField O)ˣ).card := by
      rw [Finset.card_univ, Fintype.card_units, Nat.card_eq_fintype_card]
    rw [hcu]
    refine Finset.card_le_card_of_injOn f (fun a _ => ?_) (fun a _ a' _ hf => ?_)
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, lift a • v,
        isStep_unit_smul c cK hcK hs (hunit a), (nb_unit_smul c cK hcK (hunit a)).symm,
        hmem a, rfl⟩
    · have h1 := sub_mem_of_mk_eq hϖ (hmem a) (hmem a') hf
      rw [← sub_smul] at h1
      by_contra hne
      have hne' : IsLocalRing.residue O (lift a - lift a') ≠ 0 := by
        rw [map_sub, hlift, hlift, sub_ne_zero]
        exact fun h => hne (Units.ext h)
      have hu : IsUnit (lift a - lift a') := by
        by_contra h
        exact hne' ((IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      obtain ⟨u, hu⟩ := hu
      apply hs.1
      have := L.smul_mem ((u⁻¹ : Oˣ) : O) h1
      rwa [← hu, smul_smul, Units.inv_mul, one_smul] at this
  have hn : ∀ u ∈ (Finset.univ : Finset (L.toAddSubgroup ⧸ Wg)),
      (t.filter (fun L' => rel L' u)).card ≤ Nat.card (IsLocalRing.ResidueField O) := by
    intro u _
    by_cases hE : t.filter (fun L' => rel L' u) = ∅
    · rw [hE]; simp
    obtain ⟨L0, hL0⟩ := Finset.nonempty_iff_ne_empty.2 hE
    obtain ⟨v0, hs0, -, hw0, hu0⟩ := (Finset.mem_filter.1 hL0).2
    set Wq := (perp cK J L v0).toAddSubgroup.addSubgroupOf L.toAddSubgroup with hWq
    have hcq : Nat.card (L.toAddSubgroup ⧸ Wq) = Nat.card (IsLocalRing.ResidueField O) :=
      perp_relIndex c cK hcK hϖ hL.1 hs0.1 hs0.2.1
    haveI : Finite (L.toAddSubgroup ⧸ Wq) := Nat.finite_of_card_ne_zero (by rw [hcq]; exact Nat.card_pos.ne')
    letI := Fintype.ofFinite (L.toAddSubgroup ⧸ Wq)
    have hch : ∀ L' ∈ t.filter (fun L' => rel L' u), ∃ z : L.toAddSubgroup ⧸ Wq, ∃ v,
        IsStep cK J ϖ L v ∧ L' = nb cK J L v ∧ ∃ h : v - v0 ∈ L,
          z = QuotientAddGroup.mk (⟨v - v0, h⟩ : L.toAddSubgroup) := by
      intro L' hL'
      obtain ⟨v, hs, hLv, hw, hu⟩ := (Finset.mem_filter.1 hL').2
      have h := sub_mem_of_mk_eq hϖ hw hw0 (hu.trans hu0.symm)
      exact ⟨_, v, hs, hLv, h, rfl⟩
    choose! g hg using hch
    have hinj : Set.InjOn g ↑(t.filter (fun L' => rel L' u)) := by
      intro L1 h1 L2 h2 he
      obtain ⟨v1, hs1, e1, hd1, z1⟩ := hg L1 h1
      obtain ⟨v2, hs2, e2, hd2, z2⟩ := hg L2 h2
      rw [z1, z2, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at he
      have hd : v2 - v1 ∈ perp cK J L v0 := by
        have : v2 - v1 = -(v1 - v0) + (v2 - v0) := by abel
        rw [this]; simpa using he
      have p1 := perp_congr hL.1 hd1
      have p2 := perp_congr hL.1 hd2
      rw [e1, e2]
      exact nb_congr (p1.trans p2.symm) (p1 ▸ hd)
    have hle := Finset.card_le_card_of_injOn (s := t.filter (fun L' => rel L' u))
      (t := (Finset.univ : Finset (L.toAddSubgroup ⧸ Wq))) g (fun _ _ => Finset.mem_univ _) hinj
    rw [Finset.card_univ, Fintype.card_eq_nat_card, hcq] at hle
    exact hle
  have key := Finset.card_mul_le_card_mul rel (s := t) (t := Finset.univ) hm hn
  rw [Finset.card_univ, Fintype.card_eq_nat_card, hcardW] at key
  exact key

end GlobalTheory.HermNbr
