import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

open Equiv Equiv.Perm MulAction

namespace CycleCommutantPowers

variable {α : Type} [Fintype α] [DecidableEq α]

theorem conj_pow_eq (x g : Perm α) (u : ℤ) (hx : x * g * x⁻¹ = g ^ u) :
    ∀ n : ℕ, x ^ n * g * (x ^ n)⁻¹ = g ^ (u ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have key : x ^ n * g ^ u * (x ^ n)⁻¹ = (x ^ n * g * (x ^ n)⁻¹) ^ u := by
      have h := map_zpow (MulAut.conj (x ^ n)) g u
      simpa only [MulAut.conj_apply] using h
    calc x ^ (n + 1) * g * (x ^ (n + 1))⁻¹ = x ^ n * (x * g * x⁻¹) * (x ^ n)⁻¹ := by
          first
            | (rw [pow_succ, mul_inv_rev]; simp only [mul_assoc])
            | group
      _ = x ^ n * g ^ u * (x ^ n)⁻¹ := by rw [hx]
      _ = (x ^ n * g * (x ^ n)⁻¹) ^ u := key
      _ = (g ^ (u ^ n)) ^ u := by rw [ih]
      _ = g ^ (u ^ (n + 1)) := by rw [pow_succ, zpow_mul]

theorem conj_inv_exists (x g : Perm α) (u : ℤ) (hx : x * g * x⁻¹ = g ^ u) :
    ∃ v : ℤ, x⁻¹ * g * x⁻¹⁻¹ = g ^ v := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x ^ (k + 1) = 1 :=
    ⟨orderOf x - 1, by rw [Nat.sub_add_cancel (orderOf_pos x)]; exact pow_orderOf_eq_one x⟩
  have hinv : x⁻¹ = x ^ k := by
    rw [pow_succ] at hk
    exact (eq_inv_of_mul_eq_one_left hk).symm
  refine ⟨u ^ k, ?_⟩
  rw [hinv]
  exact conj_pow_eq x g u hx k

theorem conj_key (c g : Perm α) (e : ℤ) (hc : c * g * c⁻¹ = g ^ e) (m : ℤ) :
    c * g ^ m * c⁻¹ = g ^ (e * m) := by
  have h := map_zpow (MulAut.conj c) g m
  simp only [MulAut.conj_apply] at h
  rw [h, hc, ← zpow_mul]

theorem comm_of_conj (x y g : Perm α) (u w : ℤ) (hx : x * g * x⁻¹ = g ^ u)
    (hy : y * g * y⁻¹ = g ^ w) :
    (x * y * x⁻¹ * y⁻¹) * g * (x * y * x⁻¹ * y⁻¹)⁻¹ = g := by
  obtain ⟨v, hv0⟩ := conj_inv_exists x g u hx
  obtain ⟨v', hw0⟩ := conj_inv_exists y g w hy
  have hv : x⁻¹ * g * x = g ^ v := by rw [inv_inv] at hv0; exact hv0
  have hw : y⁻¹ * g * y = g ^ v' := by rw [inv_inv] at hw0; exact hw0
  have huv : g ^ (u * v) = g := by
    rw [← conj_key x g u hx v, ← hv]
    first | group | simp [mul_assoc]
  have hwv : g ^ (w * v') = g := by
    rw [← conj_key y g w hy v', ← hw]
    first | group | simp [mul_assoc]
  have k1 := conj_key x⁻¹ g v hv0 v'
  rw [inv_inv] at k1
  have e1 : (x * y * x⁻¹ * y⁻¹) * g * (x * y * x⁻¹ * y⁻¹)⁻¹ =
      x * (y * (x⁻¹ * (y⁻¹ * g * y) * x) * y⁻¹) * x⁻¹ := by
    first | group | simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e1, hw, k1, conj_key y g w hy (v * v'), conj_key x g u hx (w * (v * v'))]
  have he : u * (w * (v * v')) = (u * v) * (w * v') := by ring
  rw [he, zpow_mul, huv, hwv]

theorem eq_zpow_on_support (g z : Perm α) (hg : g.IsCycle) (hz : z * g = g * z) :
    ∃ j : ℤ, ∀ d, g d ≠ d → z d = (g ^ j) d := by
  obtain ⟨a, ha, hcyc⟩ := hg
  have hza : g (z a) ≠ z a := by
    intro h
    apply ha
    apply z.injective
    have h2 : (z * g) a = (g * z) a := by rw [hz]
    simp only [Perm.mul_apply] at h2
    rw [h2, h]
  obtain ⟨j, hj⟩ := hcyc hza
  refine ⟨j, fun d hd => ?_⟩
  obtain ⟨i, rfl⟩ := hcyc hd
  have hcomm : z * g ^ i = g ^ i * z := ((show Commute z g from hz).zpow_right i).eq
  calc z ((g ^ i) a) = (z * g ^ i) a := rfl
    _ = (g ^ i * z) a := by rw [hcomm]
    _ = (g ^ i) (z a) := rfl
    _ = (g ^ i) ((g ^ j) a) := by rw [hj]
    _ = (g ^ i * g ^ j) a := rfl
    _ = (g ^ j * g ^ i) a := by rw [← zpow_add, ← zpow_add, add_comm]
    _ = (g ^ j) ((g ^ i) a) := rfl

theorem exists_agree (G : Subgroup (Perm α)) (Γ : Finset α)
    (hG : IsMultiplyPretransitive G α Γ.card) (π : Perm α) :
    ∃ x ∈ G, ∀ γ ∈ Γ, x γ = π γ := by
  classical
  let e : Fin Γ.card ↪ α :=
    ⟨fun i => ((Γ.equivFin.symm i : Γ) : α), fun i j h => Γ.equivFin.symm.injective (Subtype.ext h)⟩
  let e' : Fin Γ.card ↪ α := e.trans π.toEmbedding
  have hpt : IsPretransitive G (Fin Γ.card ↪ α) := hG
  obtain ⟨g, hg⟩ := hpt.exists_smul_eq e e'
  refine ⟨g, g.2, fun γ hγ => ?_⟩
  have h := congrArg (fun f : Fin Γ.card ↪ α => f (Γ.equivFin ⟨γ, hγ⟩)) hg
  have h2 : e (Γ.equivFin ⟨γ, hγ⟩) = γ := by
    show ((Γ.equivFin.symm (Γ.equivFin ⟨γ, hγ⟩) : Γ) : α) = γ
    rw [Equiv.symm_apply_apply]
  have h3 : (g : Perm α) (e (Γ.equivFin ⟨γ, hγ⟩)) = π (e (Γ.equivFin ⟨γ, hγ⟩)) := by
    first
      | exact h
      | (simp only [Function.Embedding.smul_apply, Subgroup.smul_def, Perm.smul_def] at h; exact h)
  rwa [h2] at h3

theorem sylow_adjust (G : Subgroup (Perm α)) (g : Perm α) (p : ℕ) (hp : p.Prime)
    (hgG : g ∈ G) (hgc : g.IsCycle) (hgp : g.support.card = p)
    (x : Perm α) (hxG : x ∈ G) (hxΓ : ∀ γ, g γ = γ → g (x⁻¹ γ) = x⁻¹ γ) :
    ∃ f ∈ G, (∀ γ, g γ = γ → f γ = γ) ∧ ∃ e : ℤ, (f * x) * g * (f * x)⁻¹ = g ^ e := by
  classical
  have := Fact.mk hp
  set Γ : Set α := {γ | g γ = γ} with hΓ
  set F : Subgroup (Perm α) := G ⊓ fixingSubgroup (Perm α) Γ with hF
  have memF : ∀ σ, σ ∈ F ↔ σ ∈ G ∧ ∀ γ, g γ = γ → σ γ = γ := by
    intro σ; simp [hF, mem_fixingSubgroup_iff, hΓ, Perm.smul_def]
  have hgF : g ∈ F := (memF g).2 ⟨hgG, fun γ h => h⟩
  have hcF : x * g * x⁻¹ ∈ F := by
    refine (memF _).2 ⟨G.mul_mem (G.mul_mem hxG hgG) (G.inv_mem hxG), fun γ hγ => ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, hxΓ γ hγ, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  have hcardF : Nat.card F ∣ p.factorial := by
    have hle : F ≤ (Perm.ofSubtype : Perm {x // x ∈ g.support} →* Perm α).range := by
      intro σ hσ
      obtain ⟨-, hσΓ⟩ := (memF σ).1 hσ
      have h1 : ∀ t, σ t ∈ g.support ↔ t ∈ g.support := by
        intro t
        simp only [Perm.mem_support, ne_eq, not_iff_not]
        constructor
        · intro h
          have h2 := hσΓ _ h
          have h3 : σ t = t := σ.injective h2
          rw [h3] at h; exact h
        · intro h; rw [hσΓ t h]; exact h
      refine MonoidHom.mem_range.2 ⟨σ.subtypePerm h1, ?_⟩
      apply Perm.ofSubtype_subtypePerm
      intro t ht; rw [Perm.mem_support]; intro h; exact ht (hσΓ t h)
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 := Nat.card_congr (MonoidHom.ofInjective
      (Perm.ofSubtype_injective (p := fun x => x ∈ g.support))).toEquiv
    rw [← h2, Nat.card_perm, Nat.card_eq_finsetCard, hgp] at h1
    exact h1
  have hpF : p ∣ Nat.card F := by
    have := orderOf_dvd_natCard (⟨g, hgF⟩ : F)
    rwa [← orderOf_submonoid, hgc.orderOf, hgp] at this
  have hne : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have hfact : (Nat.card F).factorization p = 1 := by
    apply le_antisymm
    · by_contra h
      push Not at h
      have h2 : p ^ 2 ∣ Nat.card F := (hp.pow_dvd_iff_le_factorization hne).2 h
      have h3 : p ^ 2 ∣ p.factorial := h2.trans hcardF
      rw [← Nat.mul_factorial_pred hp.ne_zero, pow_two] at h3
      have h4 := Nat.dvd_of_mul_dvd_mul_left hp.pos h3
      rw [hp.dvd_factorial] at h4
      have := hp.two_le
      omega
    · exact (hp.pow_dvd_iff_le_factorization hne).1 (by simpa using hpF)
  let g' : F := ⟨g, hgF⟩
  let c' : F := ⟨x * g * x⁻¹, hcF⟩
  have hc1 : Nat.card (Subgroup.zpowers g') = p ^ (Nat.card F).factorization p := by
    rw [hfact, pow_one, Nat.card_zpowers, ← orderOf_submonoid, hgc.orderOf, hgp]
  have hc2 : Nat.card (Subgroup.zpowers c') = p ^ (Nat.card F).factorization p := by
    rw [hfact, pow_one, Nat.card_zpowers, ← orderOf_submonoid]
    show orderOf (x * g * x⁻¹) = p
    rw [(hgc.conj).orderOf, Perm.card_support_conj, hgp]
  let S1 : Sylow p F := Sylow.ofCard _ hc1
  let S2 : Sylow p F := Sylow.ofCard _ hc2
  obtain ⟨f, hf⟩ := MulAction.exists_smul_eq F S2 S1
  have hmem : f * c' * f⁻¹ ∈ Subgroup.zpowers g' := by
    have h1 : c' ∈ (S2 : Subgroup F) := Subgroup.mem_zpowers c'
    have h2 : MulAut.conj f • c' ∈ ((f • S2 : Sylow p F) : Subgroup F) := by
      rw [Sylow.coe_subgroup_smul]; exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hf] at h2
    have h3 : f * c' * f⁻¹ ∈ (S1 : Subgroup F) := by simpa using h2
    exact h3
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hfF := (memF f).1 f.2
  refine ⟨f, hfF.1, hfF.2, e, ?_⟩
  have := congrArg Subtype.val he
  simp only [SubgroupClass.coe_zpow, Subgroup.coe_mul, InvMemClass.coe_inv, g', c'] at this
  rw [this]; group

end CycleCommutantPowers

theorem jordan_prime_cycle_theorem : JordanPrime := by
  intro α _ _ G g p hp hgG hgc hgp hcard hG
  classical
  set Γ : Finset α := g.supportᶜ with hΓdef
  have hmemΓ : ∀ γ, γ ∈ Γ ↔ g γ = γ := by intro γ; simp [hΓdef]
  have hΓcard : Γ.card + p = Fintype.card α := by
    rw [hΓdef, Finset.card_compl, hgp]
    have := Finset.card_le_univ g.support
    rw [hgp] at this; omega
  have hk : 3 ≤ Γ.card := by omega

  have hmt : IsMultiplyPretransitive G α Γ.card := by
    obtain ⟨m, hm⟩ : ∃ m, Γ.card = m + 1 := ⟨Γ.card - 1, by omega⟩
    have hsn : ((g.support : Set α)ᶜ).ncard = m + 1 := by
      apply Nat.add_left_cancel
      rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset, hgp, Nat.card_eq_fintype_card]
      omega
    have hsn' : m + 2 < Nat.card α := by
      rw [Nat.card_eq_fintype_card]; have := hp.two_le; omega
    have hprim : IsPreprimitive (fixingSubgroup G ((g.support : Set α)ᶜ))
        (SubMulAction.ofFixingSubgroup G ((g.support : Set α)ᶜ)) := by
      have := Equiv.Perm.isPretransitive_of_isCycle_mem hgc hgG
      apply IsPreprimitive.of_prime_card
      convert hp
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hgp]
      apply congr_arg
      ext x
      simp [SubMulAction.mem_ofFixingSubgroup_iff]
    have h1 := hG.isMultiplyPreprimitive hsn hsn' hprim
    have h2 : IsMultiplyPretransitive G α (m + 2) := IsMultiplyPreprimitive.isMultiplyPretransitive ..
    rw [hm]
    exact isMultiplyPretransitive_of_le (n := m + 2) (by omega) (by omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 (by omega : 2 < Γ.card)
  rw [hmemΓ] at ha hb hc

  have build : ∀ π : Perm α, (∀ γ, g γ = γ → g (π γ) = π γ) → π * π = 1 →
      ∃ x ∈ G, (∀ γ, g γ = γ → x γ = π γ) ∧ (∀ γ, g γ = γ → x⁻¹ γ = π γ) ∧
        ∃ e : ℤ, x * g * x⁻¹ = g ^ e := by
    intro π hπ hπ2
    have hinvOf : ∀ y : Perm α, (∀ γ, g γ = γ → y γ = π γ) → ∀ γ, g γ = γ → y⁻¹ γ = π γ := by
      intro y hy γ hγ
      rw [Perm.inv_eq_iff_eq, hy _ (hπ γ hγ), ← Perm.mul_apply, hπ2, Perm.one_apply]
    obtain ⟨x0, hx0G, hx0⟩ := CycleCommutantPowers.exists_agree G Γ hmt π
    have hx0' : ∀ γ, g γ = γ → x0 γ = π γ := fun γ hγ => hx0 γ ((hmemΓ γ).2 hγ)
    obtain ⟨f, hfG, hfΓ, e, he⟩ := CycleCommutantPowers.sylow_adjust G g p hp hgG hgc hgp x0 hx0G
      (fun γ hγ => by rw [hinvOf x0 hx0' γ hγ]; exact hπ γ hγ)
    have hfx : ∀ γ, g γ = γ → (f * x0) γ = π γ := by
      intro γ hγ
      rw [Perm.mul_apply, hx0' γ hγ, hfΓ _ (hπ γ hγ)]
    exact ⟨f * x0, G.mul_mem hfG hx0G, hfx, hinvOf _ hfx, e, he⟩
  have hswap : ∀ u v : α, g u = u → g v = v → ∀ γ, g γ = γ → g (swap u v γ) = swap u v γ := by
    intro u v hu hv γ hγ
    rw [swap_apply_def]
    split_ifs <;> assumption
  obtain ⟨x, hxG, hx, hxi, u, hu⟩ := build (swap a b) (hswap a b ha hb) (swap_mul_self a b)
  obtain ⟨y, hyG, hy, hyi, w, hw⟩ := build (swap a c) (hswap a c ha hc) (swap_mul_self a c)
  set z := x * y * x⁻¹ * y⁻¹ with hzdef
  have hzG : z ∈ G := G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)
  have hz : z * g * z⁻¹ = g := CycleCommutantPowers.comm_of_conj x y g u w hu hw
  have hzc : z * g = g * z := by
    calc z * g = z * g * z⁻¹ * z := by group
      _ = g * z := by rw [hz]
  obtain ⟨j, hj⟩ := CycleCommutantPowers.eq_zpow_on_support g z hgc hzc
  set t := swap a b * swap a c with htdef
  have h3 : IsThreeCycle t := isThreeCycle_swap_mul_swap_same hab hac hbc
  have hwt : g ^ (-j) * z = t * t := by
    ext d
    by_cases hd : g d = d
    ·
      have hzd : z d = swap a b (swap a c (swap a b (swap a c d))) := by
        have e1 := hswap a c ha hc d hd
        have e2 := hswap a b ha hb _ e1
        have e3 := hswap a c ha hc _ e2
        simp only [hzdef, Perm.mul_apply]
        rw [hyi d hd, hxi _ e1, hy _ e2, hx _ e3]
      have hzΓ : g (z d) = z d := by
        rw [hzd]
        exact hswap a b ha hb _ (hswap a c ha hc _ (hswap a b ha hb _ (hswap a c ha hc d hd)))
      rw [Perm.mul_apply, zpow_apply_eq_self_of_apply_eq_self hzΓ, hzd, htdef]
      simp only [Perm.mul_apply]
    ·
      have hda : d ≠ a := fun h => hd (h ▸ ha)
      have hdb : d ≠ b := fun h => hd (h ▸ hb)
      have hdc : d ≠ c := fun h => hd (h ▸ hc)
      rw [Perm.mul_apply, hj d hd, ← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
        Perm.one_apply, htdef]
      simp only [Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hda hdc, swap_apply_of_ne_of_ne hda hdb,
        swap_apply_of_ne_of_ne hda hdc, swap_apply_of_ne_of_ne hda hdb]
  have htt : t * t = t⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h := pow_orderOf_eq_one t
    rw [h3.isCycle.orderOf, h3.card_support] at h
    rw [← h, pow_three', mul_assoc]
  have hwG : g ^ (-j) * z ∈ G := G.mul_mem (G.zpow_mem hgG _) hzG
  rw [hwt, htt] at hwG
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG h3.inv hwG

end Formalism.GaloisIrreducibility
