import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

open Finset

theorem card_pow_eq_one_le_two_mul {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [IsCyclic H] (hH : H.index ≤ 2) {D : ℕ} (hD : 0 < D) :
    #{a : G | a ^ D = 1} ≤ 2 * D := by
  classical
  set S : Subgroup G := (powMonoidHom D : G →* G).ker with hSdef
  have hmem : ∀ a : G, a ∈ S ↔ a ^ D = 1 := fun a => by simp [hSdef]
  have hcardS : #{a : G | a ^ D = 1} = Nat.card S := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun a => (hmem a).symm))
  rw [hcardS]
  have hK : IsCyclic (H ⊓ S : Subgroup G) := Subgroup.isCyclic_of_le inf_le_left
  have h1 : Nat.card (H ⊓ S : Subgroup G) ≤ D := by
    rw [← IsCyclic.exponent_eq_card]
    apply Nat.le_of_dvd hD
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    have : (g : G) ^ D = 1 := (hmem g).1 g.2.2
    ext; simpa using this
  have h2 : H.relIndex S ≤ 2 := by
    have hd := Subgroup.relIndex_dvd_index_of_normal H S
    have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd).trans hH
  have h3 : Nat.card (H ⊓ S : Subgroup G) * H.relIndex S = Nat.card S := by
    have := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (H ⊓ S) S bot_le inf_le_right
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at this
    exact this
  rw [← h3]
  calc Nat.card (H ⊓ S : Subgroup G) * H.relIndex S ≤ D * 2 := Nat.mul_le_mul h1 h2
    _ = 2 * D := by ring

theorem card_residues_le_units (n D : ℕ) [NeZero n] (hD : 0 < D) :
    ((Finset.range n).filter (fun x => x ^ D ≡ 1 [MOD n])).card ≤
      #{u : (ZMod n)ˣ | u ^ D = 1} := by
  classical
  have step1 : ((Finset.range n).filter (fun x => x ^ D ≡ 1 [MOD n])).card ≤
      #{y : ZMod n | y ^ D = 1} := by
    apply Finset.card_le_card_of_injOn (fun x : ℕ => (x : ZMod n))
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      have := (ZMod.natCast_eq_natCast_iff (x ^ D) 1 n).2 hx.2
      push_cast at this
      exact this
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx hy
      have h := congrArg ZMod.val hxy
      simp only [ZMod.val_natCast] at h
      rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h
  refine step1.trans ?_
  have hsub : ({y : ZMod n | y ^ D = 1} : Finset (ZMod n)) ⊆
      Finset.image (fun u : (ZMod n)ˣ => (u : ZMod n))
        (Finset.univ.filter (fun u : (ZMod n)ˣ => u ^ D = 1)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : y * y ^ (D - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hD, hy]
    refine ⟨⟨y, y ^ (D - 1), h1, by rw [mul_comm]; exact h1⟩, ?_, rfl⟩
    ext; simpa using hy
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem index_zpowers_five (n : ℕ) (h : Nat.Coprime 5 (2 ^ (n + 2))) :
    (Subgroup.zpowers (ZMod.unitOfCoprime 5 h)).index = 2 := by
  have hc := Subgroup.card_mul_index (Subgroup.zpowers (ZMod.unitOfCoprime 5 h))
  rw [Nat.card_zpowers, ← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat,
    ZMod.orderOf_five, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega)] at hc
  have : 2 ^ (n + 2 - 1) * (2 - 1) = 2 ^ n * 2 := by
    rw [show n + 2 - 1 = n + 1 by omega, pow_succ]; norm_num
  rw [this] at hc
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hc

theorem residues_count_le : ResiduesLe := by
  classical
  intro l j D hl hD
  have hD0 : 0 < D := hD
  have : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.ne_zero⟩
  refine (card_residues_le_units (l ^ j) D hD0).trans ?_
  by_cases hcyc : IsCyclic (ZMod (l ^ j))ˣ
  · exact card_pow_eq_one_le_two_mul (⊤ : Subgroup (ZMod (l ^ j))ˣ)
      (by rw [Subgroup.index_top]; norm_num) hD0
  · have hl2 : l = 2 := by
      by_contra hne
      exact hcyc (ZMod.isCyclic_units_of_prime_pow l hl hne j)
    subst hl2
    have hj : ¬ j ≤ 2 := fun hj => hcyc ((ZMod.isCyclic_units_two_pow_iff j).2 hj)
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
    have h5 : Nat.Coprime 5 (2 ^ (n + 2)) :=
      Nat.Coprime.pow_right _ (by norm_num)
    exact card_pow_eq_one_le_two_mul (Subgroup.zpowers (ZMod.unitOfCoprime 5 h5))
      (by rw [index_zpowers_five n h5]) hD0

end Formalism.GaloisIrreducibility
