import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfNotDvd

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem mem_nb {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)}
    {v x : Fin r → K} : x ∈ nb cK J L v ↔ ∃ m ∈ perp cK J L v, ∃ a : O, x = m + a • v := by
  unfold nb
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨m, hm, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨m, hm, a, rfl⟩
  · rintro ⟨m, hm, a, rfl⟩
    exact ⟨m, hm, a • v, Submodule.mem_span_singleton.2 ⟨a, rfl⟩, rfl⟩

theorem conj_mem_range (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) {y : K}
    (hy : y ∈ (algebraMap O K).range) : cK y ∈ (algebraMap O K).range := by
  obtain ⟨a, rfl⟩ := hy
  exact ⟨c a, (hcK a).symm⟩

theorem nb_int (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hvv : hf cK J v v ∈ (algebraMap O K).range) {x y : Fin r → K}
    (hx : x ∈ nb cK J L v) (hy : y ∈ nb cK J L v) :
    hf cK J x y ∈ (algebraMap O K).range := by
  obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hx
  obtain ⟨m', hm', a', rfl⟩ := mem_nb.1 hy
  rw [mem_perp] at hm hm'
  have h1 : hf cK J m m' ∈ (algebraMap O K).range := (hSD m).1 hm.1 m' hm'.1
  have h2 : hf cK J m v ∈ (algebraMap O K).range := by
    rw [hf_conj cK hc2 J hJ]; exact conj_mem_range c cK hcK hm.2
  rw [hf_add_left, hf_add_right, hf_add_right, hf_algSmul_right, hf_algSmul_left,
    hf_algSmul_left, hf_algSmul_right, hcK]
  refine add_mem (add_mem h1 (mul_mem ⟨_, rfl⟩ h2)) (add_mem (mul_mem ⟨_, rfl⟩ hm'.2) ?_)
  exact mul_mem ⟨_, rfl⟩ (mul_mem ⟨_, rfl⟩ hvv)

theorem nb_sd (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) : IsSD cK J (nb cK J L v) := by
  obtain ⟨hv, hw, hvv⟩ := hstep
  intro x
  refine ⟨fun hx y hy => nb_int c cK hcK hc2 hJ hϖ hSD hvv hx hy, fun hx => ?_⟩
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  have hβ' : algebraMap O K ϖ * hf cK J v l0 ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
  have hperp_nb : ∀ m ∈ perp cK J L v, m ∈ nb cK J L v := fun m hm =>
    mem_nb.2 ⟨m, hm, 0, by simp⟩
  have hl0p : ϖ • l0 ∈ perp cK J L v := by
    refine mem_perp.2 ⟨L.smul_mem ϖ hl0, ?_⟩
    rw [hf_algSmul_right]; exact hβ'
  have hxl0 : algebraMap O K ϖ * hf cK J x l0 ∈ (algebraMap O K).range := by
    have := hx _ (hperp_nb _ hl0p)
    rwa [hf_algSmul_right] at this
  obtain ⟨e, he⟩ := exists_ratio hϖ hβ hβ' hxl0
  set b := c.symm e with hb
  have hcb : cK (algebraMap O K b) = algebraMap O K e := by rw [hcK, hb, RingEquiv.apply_symm_apply]
  set x' := x - b • v with hx'
  have hx'l0 : hf cK J x' l0 = 0 := by
    rw [hx', hf_sub_left, hf_algSmul_left, hcb, he, sub_self]
  have hx'm : ∀ m ∈ perp cK J L v, hf cK J x' m ∈ (algebraMap O K).range := by
    intro m hm
    rw [hx', hf_sub_left, hf_algSmul_left]
    exact sub_mem (hx m (hperp_nb m hm)) (mul_mem (conj_mem_range c cK hcK ⟨_, rfl⟩) (mem_perp.1 hm).2)
  have hx'L : x' ∈ L := by
    refine (hSD x').2 fun l hl => ?_
    obtain ⟨a, ha⟩ := exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw hl)
    have hm : l - a • l0 ∈ perp cK J L v := by
      refine mem_perp.2 ⟨L.sub_mem hl (L.smul_mem a hl0), ?_⟩
      rw [hf_sub_right, hf_algSmul_right, ha, sub_self]
      exact zero_mem _
    have : l = (l - a • l0) + a • l0 := by abel
    rw [this, hf_add_right, hf_algSmul_right, hx'l0, mul_zero, add_zero]
    exact hx'm _ hm
  have hx'p : x' ∈ perp cK J L v := by
    refine mem_perp.2 ⟨hx'L, ?_⟩
    rw [hf_conj cK hc2 J hJ]
    apply conj_mem_range c cK hcK
    rw [hx', hf_sub_left, hf_algSmul_left]
    exact sub_mem (hx v hvnb) (mul_mem (conj_mem_range c cK hcK ⟨_, rfl⟩) hvv)
  exact mem_nb.2 ⟨x', hx'p, b, by rw [hx']; abel⟩

theorem perp_eq_perp_nb (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) {l0 : Fin r → K} (hl0 : l0 ∈ L)
    (hβ : hf cK J v l0 ∉ (algebraMap O K).range) :
    perp cK J L v = perp cK J (nb cK J L v) l0 := by
  have hSDn := nb_sd c cK hcK hc2 hJ hϖ hSD hstep
  obtain ⟨hv, hw, hvv⟩ := hstep
  have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
  ext x
  constructor
  · intro hx
    refine mem_perp.2 ⟨mem_nb.2 ⟨x, hx, 0, by simp⟩, (hSD l0).1 hl0 x (mem_perp.1 hx).1⟩
  · intro hx
    obtain ⟨hxn, hxl⟩ := mem_perp.1 hx
    obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hxn
    have hm' := mem_perp.1 hm
    have h1 : algebraMap O K a * hf cK J l0 v ∈ (algebraMap O K).range := by
      rw [hf_add_right, hf_algSmul_right] at hxl
      have := sub_mem hxl ((hSD l0).1 hl0 m hm'.1)
      simpa using this
    have hγ : hf cK J l0 v ∉ (algebraMap O K).range := by
      intro h
      apply hβ
      rw [hf_conj cK hc2 J hJ l0 v]
      exact conj_mem_range c cK hcK h
    have hγ' : algebraMap O K ϖ * hf cK J l0 v ∈ (algebraMap O K).range := by
      rw [← hf_algSmul_right]; exact (hSD l0).1 hl0 _ hw
    obtain ⟨e, rfl⟩ := (ratio_mem_iff hϖ hγ hγ' a).1 h1
    refine mem_perp.2 ⟨?_, (hSDn v).1 hvnb _ hxn⟩
    rw [mul_comm ϖ e, mul_smul]
    exact L.add_mem hm'.1 (L.smul_mem e hw)

theorem good_nb (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField O)] {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) : Good cK J ϖ N (nb cK J L v) := by
  obtain ⟨hSD, habs, hidx⟩ := hL
  have hSDn := nb_sd c cK hcK hc2 hJ hϖ hSD hstep
  obtain ⟨hv, hw, hvv⟩ := hstep
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  have hβ' : algebraMap O K ϖ * hf cK J v l0 ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hQ : Nat.card (IsLocalRing.ResidueField O) ≠ 0 := Nat.card_pos.ne'
  have hpL : perp cK J L v ≤ L := fun x hx => (mem_perp.1 hx).1
  have hpn : perp cK J L v ≤ nb cK J L v := fun x hx => mem_nb.2 ⟨x, hx, 0, by simp⟩
  have i1 := perp_relIndex c cK hcK hϖ hSD hv hw
  have hl0n : l0 ∉ nb cK J L v := by
    intro h
    have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
    exact hβ ((hSDn v).1 hvnb l0 h)
  have hwl0 : ϖ • l0 ∈ nb cK J L v := by
    refine hpn (mem_perp.2 ⟨L.smul_mem ϖ hl0, ?_⟩)
    rw [hf_algSmul_right]; exact hβ'
  have i2 := perp_relIndex c cK hcK hϖ hSDn hl0n hwl0
  rw [← perp_eq_perp_nb c cK hcK hc2 hJ hϖ hSD ⟨hv, hw, hvv⟩ hl0 hβ] at i2
  refine ⟨hSDn, ?_, ?_⟩
  · intro x
    obtain ⟨k, hk⟩ := habs x
    refine ⟨k + 1, hpn (mem_perp.2 ⟨?_, ?_⟩)⟩
    · rw [pow_succ', mul_smul]; exact L.smul_mem ϖ hk
    · rw [pow_succ', mul_smul, hf_algSmul_right]
      exact mul_pair_mem c cK hcK hϖ hSD hw hk
  · rw [← idx_eq_of_le hϖ hpn (by rw [i2]; exact hQ), idx_eq_of_le hϖ hpL (by rw [i1]; exact hQ),
      hidx]

end GlobalTheory.HermNbr
