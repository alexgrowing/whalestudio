import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.TameInertiaTowers.TowerFieldFoundations

open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Galois

section Roots

variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}

theorem pow_val_eq_iff (hζ : IsPrimitiveRoot ζ N) (k j : ZMod N) :
    ζ ^ k.val = ζ ^ j.val ↔ k = j := by
  constructor
  · intro hkj
    exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt j) hkj)
  · rintro rfl
    rfl

theorem pow_val_mul_eq_one_iff (hζ : IsPrimitiveRoot ζ N) (k j : ZMod N) :
    ζ ^ k.val * ζ ^ j.val = 1 ↔ k + j = 0 := by
  rw [← pow_add, hζ.pow_eq_one_iff_dvd, ← CharP.cast_eq_zero_iff (ZMod N) N, Nat.cast_add,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem pow_val_neg (hζ : IsPrimitiveRoot ζ N) (k : ZMod N) :
    ζ ^ (-k).val = ζ⁻¹ ^ k.val := by
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left ((pow_val_mul_eq_one_iff hζ (-k) k).2 (by ring))

theorem trace_eq_iff (hζ : IsPrimitiveRoot ζ N) (u c : ZMod N) :
    ζ ^ u.val + ζ⁻¹ ^ u.val = ζ ^ c.val + ζ⁻¹ ^ c.val ↔ u = c ∨ u = -c := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)

  have key : ∀ x y : K, x ≠ 0 → y ≠ 0 → (x + x⁻¹ = y + y⁻¹ ↔ x = y ∨ x * y = 1) := by
    intro x y hx hy
    have hx' : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    have hy' : y * y⁻¹ = 1 := mul_inv_cancel₀ hy
    have e : (x - y) * (x * y - 1) = x * y * ((x + x⁻¹) - (y + y⁻¹)) := by
      linear_combination (-y) * hx' + x * hy'
    constructor
    · intro hxy
      rw [hxy, sub_self, mul_zero] at e
      rcases mul_eq_zero.1 e with h1 | h1
      · exact Or.inl (sub_eq_zero.1 h1)
      · exact Or.inr (sub_eq_zero.1 h1)
    · rintro (h1 | h1)
      · rw [h1]
      · rw [eq_inv_of_mul_eq_one_right h1, inv_inv, add_comm]
  rw [inv_pow, inv_pow, key _ _ (pow_ne_zero _ h0) (pow_ne_zero _ h0), pow_val_eq_iff hζ,
    pow_val_mul_eq_one_iff hζ, eq_neg_iff_add_eq_zero]

theorem trace_eq_iff_units (hζ : IsPrimitiveRoot ζ N) (u c : (ZMod N)ˣ) :
    ζ ^ (u : ZMod N).val + ζ⁻¹ ^ (u : ZMod N).val = ζ ^ (c : ZMod N).val + ζ⁻¹ ^ (c : ZMod N).val ↔
      u = c ∨ u = -c := by
  rw [trace_eq_iff hζ, Units.ext_iff, Units.ext_iff, Units.val_neg]

theorem mem_zpowers_neg_one (x : (ZMod N)ˣ) :
    x ∈ Subgroup.zpowers (-1 : (ZMod N)ˣ) ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl hk.neg_one_zpow
    · exact Or.inr hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

end Roots

theorem hcl_eq_iff (e : ℕ) (u c : (ZMod (2 ^ (e + 2)))ˣ) :
    hcl e u = hcl e c ↔ u = c ∨ u = -c := by
  unfold hcl
  change ((u : (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1)) = c) ↔ _
  rw [QuotientGroup.eq, mem_zpowers_neg_one, inv_mul_eq_one, inv_mul_eq_iff_eq_mul, mul_neg_one]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, neg_neg]
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, neg_neg]

section Layer

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem layer_galois (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    IsGalois ℚ L ∧ Module.finrank ℚ L = 2 ^ (e + 2 + 1) ∧
    (∀ σ τ : Gal(L/ℚ), galMap h.1 a b (σ * τ) = galMap h.1 a b σ * galMap h.1 a b τ) ∧
    Function.Bijective (galMap h.1 a b) :=
  layerGalois (e + 2) q d (by omega) hqd L ζ a b h

theorem galMap_one (h : IsLayer (e + 2) q d ζ a b) :
    galMap h.1 a b (1 : Gal(L/ℚ)) = 1 := by
  have hs : ∀ x : L, sgn (1 : Gal(L/ℚ)) x = 1 := fun x => by
    rw [sgn.eq_1, if_pos (AlgEquiv.one_apply x)]
  rw [galMap.eq_1, map_one, hs, hs]
  rfl

theorem fix_of_sgn_one {K : Type*} [Field K] [Algebra ℚ K] {σ : Gal(K/ℚ)} {x : K}
    (hs : sgn σ x = 1) : σ x = x := by
  rw [sgn.eq_1] at hs
  by_contra hne
  rw [if_neg hne] at hs
  exact absurd (congrArg Units.val hs) (by norm_num)

theorem gal_mul_comm_of_isLayer (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (σ τ : Gal(L/ℚ)) :
    σ * τ = τ * σ := by
  obtain ⟨-, -, hmul, hbij⟩ := layer_galois hqd h
  apply hbij.1
  rw [hmul, hmul, mul_comm]

def tau0 (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : Gal(L/ℚ) :=
  ((layer_galois hqd h).2.2.2.2 ((-1, 1, 1) : GalL (e + 2))).choose

theorem galMap_zeta_inversion (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    galMap h.1 a b (tau0 hqd h) = ((-1, 1, 1) : GalL (e + 2)) := by
  exact ((layer_galois hqd h).2.2.2.2 ((-1, 1, 1) : GalL (e + 2))).choose_spec

theorem galMap_eq_neg_one_one_one_iff_eq_zeta_inversion (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (τ : Gal(L/ℚ)) :
    galMap h.1 a b τ = ((-1, 1, 1) : GalL (e + 2)) ↔ τ = tau0 hqd h := by
  constructor
  · intro hτ
    exact (layer_galois hqd h).2.2.2.1 (hτ.trans (galMap_zeta_inversion hqd h).symm)
  · rintro rfl
    exact galMap_zeta_inversion hqd h

theorem apply_theta {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) (τ : Gal(L/ℚ)) :
    τ (ζ + ζ⁻¹) = ζ ^ (hζ.autToPow ℚ τ : ZMod N).val + ζ⁻¹ ^ (hζ.autToPow ℚ τ : ZMod N).val := by
  rw [map_add, map_inv₀, ← hζ.autToPow_spec ℚ τ, inv_pow]

theorem two_lt (e : ℕ) : 2 < 2 ^ (e + 2) := by
  have h4 : 2 ^ 2 ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (e + 2) := h4

theorem one_val (e : ℕ) : (1 : ZMod (2 ^ (e + 2))).val = 1 := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (lt_trans one_lt_two (two_lt e))]

private theorem autToPow_tau0_eq_neg_one (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    h.1.autToPow ℚ (tau0 hqd h) = -1 := by
  have h1 := galMap_zeta_inversion hqd h
  rw [galMap.eq_1] at h1
  exact congrArg Prod.fst h1

theorem zeta_inversion_fixes_zeta_add_inv (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    tau0 hqd h (ζ + ζ⁻¹) = ζ + ζ⁻¹ := by
  rw [apply_theta h.1, autToPow_tau0_eq_neg_one hqd h, Units.val_neg, Units.val_one, pow_val_neg h.1,
    pow_val_neg h.1.inv, inv_inv, one_val, pow_one, pow_one, add_comm]

theorem zeta_inversion_fixes_a (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : tau0 hqd h a = a := by
  apply fix_of_sgn_one
  have h1 := galMap_zeta_inversion hqd h
  rw [galMap.eq_1] at h1
  exact congrArg (fun g => g.2.1) h1

theorem zeta_inversion_fixes_b (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : tau0 hqd h b = b := by
  apply fix_of_sgn_one
  have h1 := galMap_zeta_inversion hqd h
  rw [galMap.eq_1] at h1
  exact congrArg (fun g => g.2.2) h1

theorem zeta_inversion_ne_one (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : tau0 hqd h ≠ 1 := by
  intro h1
  haveI : Fact (2 < 2 ^ (e + 2)) := ⟨two_lt e⟩
  have hz := h.1.autToPow_spec ℚ (tau0 hqd h)
  rw [autToPow_tau0_eq_neg_one hqd h, h1, AlgEquiv.one_apply, Units.val_neg, Units.val_one] at hz
  have h2 : ζ ^ (-1 : ZMod (2 ^ (e + 2))).val = ζ ^ (1 : ZMod (2 ^ (e + 2))).val := by
    rw [hz, one_val, pow_one]
  exact ZMod.neg_one_ne_one ((pow_val_eq_iff h.1 _ _).1 h2)

theorem zeta_inversion_sq_eq_one (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : tau0 hqd h ^ 2 = 1 := by
  apply (layer_galois hqd h).2.2.2.1
  have hA : (tau0 hqd h ^ 2) a = a := by rw [pow_two, AlgEquiv.mul_apply, zeta_inversion_fixes_a, zeta_inversion_fixes_a]
  have hB : (tau0 hqd h ^ 2) b = b := by rw [pow_two, AlgEquiv.mul_apply, zeta_inversion_fixes_b, zeta_inversion_fixes_b]
  have hU : h.1.autToPow ℚ (tau0 hqd h ^ 2) = h.1.autToPow ℚ 1 := by
    rw [map_pow, map_one, autToPow_tau0_eq_neg_one hqd h, neg_one_sq]
  rw [galMap.eq_1, galMap.eq_1, hU, sgn.eq_1, sgn.eq_1, sgn.eq_1, sgn.eq_1, if_pos hA, if_pos hB,
    if_pos (AlgEquiv.one_apply a), if_pos (AlgEquiv.one_apply b)]

theorem orderOf_zeta_inversion (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    orderOf (tau0 hqd h) = 2 := by
  exact orderOf_eq_prime (zeta_inversion_sq_eq_one hqd h) (zeta_inversion_ne_one hqd h)

theorem mem_fixedField_zpowers (τ : Gal(L/ℚ)) (x : L) :
    x ∈ fixedField (Subgroup.zpowers τ) ↔ τ x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx
    exact hx τ (Subgroup.mem_zpowers τ)
  · intro hx f hf
    have hle : Subgroup.zpowers τ ≤ MulAction.stabilizer Gal(L/ℚ) x := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hx
    exact MulAction.mem_stabilizer_iff.1 (hle hf)

end Layer

section Host

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem hostE_eq_adjoin (ζ a b : L) : hostE ζ a b = ℚ⟮ζ + ζ⁻¹, a, b⟯ := by
  rw [hostE.eq_1, E0.eq_1, F1.eq_1, ← IntermediateField.adjoin_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem hostE_le_fixedField (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    hostE ζ a b ≤ fixedField (Subgroup.zpowers (tau0 hqd h)) := by
  rw [hostE_eq_adjoin, IntermediateField.adjoin_le_iff]
  intro x hx
  rw [SetLike.mem_coe, mem_fixedField_zpowers]
  rcases hx with rfl | rfl | rfl
  · exact zeta_inversion_fixes_zeta_add_inv hqd h
  · exact zeta_inversion_fixes_a hqd h
  · exact zeta_inversion_fixes_b hqd h

theorem fixingSubgroup_hostE_le (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    (hostE ζ a b).fixingSubgroup ≤ Subgroup.zpowers (tau0 hqd h) := by
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have mem : ∀ y ∈ ({ζ + ζ⁻¹, a, b} : Set L), y ∈ hostE ζ a b := by
    intro y hy
    rw [hostE_eq_adjoin]
    exact IntermediateField.subset_adjoin ℚ _ hy
  have hθ := hσ _ (mem _ (Set.mem_insert _ _))
  have ha := hσ _ (mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hb := hσ _ (mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  rw [apply_theta h.1] at hθ
  have hc : h.1.autToPow ℚ σ = 1 ∨ h.1.autToPow ℚ σ = -1 := by
    rw [← trace_eq_iff_units h.1, hθ, Units.val_one, one_val, pow_one, pow_one]
  have hsa : sgn σ a = 1 := by rw [sgn.eq_1, if_pos ha]
  have hsb : sgn σ b = 1 := by rw [sgn.eq_1, if_pos hb]
  have hbij := (layer_galois hqd h).2.2.2
  rcases hc with hc | hc
  · have h1 : σ = 1 := by
      apply hbij.1
      rw [galMap.eq_1, galMap.eq_1, hc, hsa, hsb, map_one, sgn.eq_1, sgn.eq_1,
        if_pos (AlgEquiv.one_apply a), if_pos (AlgEquiv.one_apply b)]
    rw [h1]
    exact Subgroup.one_mem _
  · have h1 : σ = tau0 hqd h := by
      rw [← galMap_eq_neg_one_one_one_iff_eq_zeta_inversion hqd h, galMap.eq_1, hc, hsa, hsb]
    rw [h1]
    exact Subgroup.mem_zpowers _

theorem hostE_eq_fixedField (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    hostE ζ a b = fixedField (Subgroup.zpowers (tau0 hqd h)) := by
  haveI := (layer_galois hqd h).1
  have hfix : (hostE ζ a b).fixingSubgroup = Subgroup.zpowers (tau0 hqd h) :=
    le_antisymm (fixingSubgroup_hostE_le hqd h)
      ((IntermediateField.le_iff_le _ _).1 (hostE_le_fixedField hqd h))
  rw [← hfix, IsGalois.fixedField_fixingSubgroup]

theorem mem_hostE_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (x : L) :
    x ∈ hostE ζ a b ↔ tau0 hqd h x = x := by
  rw [hostE_eq_fixedField hqd h, mem_fixedField_zpowers]

theorem finrank_cmField (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Module.finrank ℚ (hostE ζ a b) = 2 ^ (e + 2) := by
  haveI := (layer_galois hqd h).1
  have hL := (layer_galois hqd h).2.1
  rw [hostE_eq_fixedField hqd h]
  have h1 := Module.finrank_mul_finrank ℚ (fixedField (Subgroup.zpowers (tau0 hqd h))) L
  rw [IntermediateField.finrank_fixedField_eq_card, hL] at h1
  simp only [Nat.card_zpowers, Fintype.card_zpowers, orderOf_zeta_inversion hqd h] at h1
  rw [pow_succ] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1

theorem isGalois_hostE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    IsGalois ℚ (hostE ζ a b) := by
  haveI := (layer_galois hqd h).1
  haveI : (Subgroup.zpowers (tau0 hqd h)).Normal :=
    ⟨fun n hn g => by rwa [gal_mul_comm_of_isLayer hqd h g n, mul_inv_cancel_right]⟩
  rw [hostE_eq_fixedField hqd h]
  exact IsGalois.of_fixedField_normal_subgroup _

theorem exists_lift (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    ∃ τ : Gal(L/ℚ), ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x := by
  haveI := (layer_galois hqd h).1
  exact ⟨σ.liftNormal L, fun x => (σ.liftNormal_commutes L x).symm⟩

theorem exists_restrict (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (τ : Gal(L/ℚ)) :
    ∃ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x := by
  haveI := (layer_galois hqd h).1
  haveI := isGalois_hostE hqd h
  exact ⟨τ.restrictNormal (hostE ζ a b), fun x => τ.restrictNormal_commutes (hostE ζ a b) x⟩

theorem sgn_lift {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b} {τ : Gal(L/ℚ)}
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (x : hostE ζ a b) :
    sgn σ x = sgn τ (x : L) := by
  have key : σ x = x ↔ τ (x : L) = x := by
    rw [← hστ x]
    exact Subtype.ext_iff
  rw [sgn.eq_1, sgn.eq_1]
  by_cases hx : σ x = x
  · rw [if_pos hx, if_pos (key.1 hx)]
  · rw [if_neg hx, if_neg (fun h' => hx (key.2 h'))]

theorem hPart_lift (h : IsLayer (e + 2) q d ζ a b) {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b}
    {τ : Gal(L/ℚ)} (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) :
    hPart e ζ a b σ = hcl e (h.1.autToPow ℚ τ) := by
  have hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ (h.1.autToPow ℚ τ : ZMod (2 ^ (e + 2))).val +
        ζ⁻¹ ^ (h.1.autToPow ℚ τ : ZMod (2 ^ (e + 2))).val := by
    rw [hστ]; exact apply_theta h.1 τ
  have hex : ∃ u : (ZMod (2 ^ (e + 2)))ˣ, ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val := ⟨_, hθ⟩
  unfold hPart
  rw [dif_pos hex, hcl_eq_iff]
  have hs := hθ.symm.trans hex.choose_spec
  exact (trace_eq_iff_units h.1 _ _).mp hs.symm

theorem galE_lift (h : IsLayer (e + 2) q d ζ a b) {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b}
    {τ : Gal(L/ℚ)} (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) :
    galE e ζ a b σ =
      (((galMap h.1 a b τ).2.1, (galMap h.1 a b τ).2.2), hcl e (galMap h.1 a b τ).1) := by
  rw [galE.eq_1, hPart_lift h hστ, sgn_lift hστ (aE ζ a b), sgn_lift hστ (bE ζ a b), galMap.eq_1]
  rfl

end Host

end Galois

open Galois

theorem hostFixed : HostFixed := by
  unfold HostFixed
  intro e q d hqd L _ _ ζ a b h
  refine ⟨hostE_eq_adjoin ζ a b, fun x => ?_⟩
  rw [mem_hostE_iff hqd h]
  constructor
  · intro hx τ hτ
    rw [(galMap_eq_neg_one_one_one_iff_eq_zeta_inversion hqd h τ).1 hτ]
    exact hx
  · intro H
    exact H _ (galMap_zeta_inversion hqd h)

theorem hostGalois : HostGalois := by
  unfold HostGalois
  intro e q d hqd L _ _ ζ a b h
  haveI := (layer_galois hqd h).1
  obtain ⟨-, -, hmul, hbij⟩ := layer_galois hqd h
  refine ⟨isGalois_hostE hqd h, finrank_cmField hqd h, fun σ τ => ?_, ⟨fun σ σ' hss => ?_, fun y => ?_⟩⟩
  · obtain ⟨τ1, h1⟩ := exists_lift hqd h σ
    obtain ⟨τ2, h2⟩ := exists_lift hqd h τ
    have h12 : ∀ x : hostE ζ a b, (((σ * τ) x : hostE ζ a b) : L) = (τ1 * τ2) (x : L) := by
      intro x
      rw [AlgEquiv.mul_apply, h1, h2]
      rfl
    rw [galE_lift h h12, galE_lift h h1, galE_lift h h2, hmul]
    rfl
  · obtain ⟨τ1, h1⟩ := exists_lift hqd h σ
    obtain ⟨τ2, h2⟩ := exists_lift hqd h σ'
    rw [galE_lift h h1, galE_lift h h2] at hss
    have ha : (galMap h.1 a b τ1).2.1 = (galMap h.1 a b τ2).2.1 := congrArg (fun z => z.1.1) hss
    have hb : (galMap h.1 a b τ1).2.2 = (galMap h.1 a b τ2).2.2 := congrArg (fun z => z.1.2) hss
    have hc := (hcl_eq_iff e _ _).1 (congrArg Prod.snd hss)
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [h1, h2]
    rcases hc with hc | hc
    · have h3 : τ1 = τ2 := hbij.1 (Prod.ext hc (Prod.ext ha hb))
      rw [h3]
    · have h3 : τ1 = τ2 * tau0 hqd h := by
        apply hbij.1
        rw [hmul, galMap_zeta_inversion hqd h]
        exact Prod.ext (by rw [hc]; exact (mul_neg_one _).symm)
          (Prod.ext (ha.trans (mul_one _).symm) (hb.trans (mul_one _).symm))
      rw [h3, AlgEquiv.mul_apply, (mem_hostE_iff hqd h _).1 x.2]
  · obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective y.2
    obtain ⟨τ, hτ⟩ := hbij.2 ((u, y.1.1, y.1.2) : GalL (e + 2))
    obtain ⟨σ, hσ⟩ := exists_restrict hqd h τ
    refine ⟨σ, ?_⟩
    rw [galE_lift h hσ, hτ]
    exact Prod.ext rfl hu

private theorem apply_eq_sgn_mul_of_apply_sq_eq_sq {K : Type*} [Field K] [Algebra ℚ K] (σ : Gal(K/ℚ)) (x : K)
    (hx : σ (x ^ 2) = x ^ 2) : σ x = ((sgn σ x : ℤ) : K) * x := by
  rw [sgn.eq_1]
  by_cases hs : σ x = x
  · rw [if_pos hs, Units.val_one, Int.cast_one, one_mul, hs]
  · rw [if_neg hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    rw [map_pow] at hx
    have h2 : (σ x - x) * (σ x + x) = 0 := by linear_combination hx
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hs
    · exact eq_neg_of_add_eq_zero_left h1

theorem hostGalSpec : HostGalSpec := by
  unfold HostGalSpec
  intro e q d hqd L _ _ ζ a b h σ
  obtain ⟨τ, hστ⟩ := exists_lift hqd h σ
  have hsq : ∀ y : L, ∀ r : ℕ, y ^ 2 = -(r : L) → τ (y ^ 2) = y ^ 2 := by
    intro y r hy
    rw [hy, map_neg, map_natCast]
  refine ⟨?_, ?_, fun u => ?_, fun τ' hτ' => galE_lift h hτ'⟩
  · rw [galE.eq_1, hστ (aE ζ a b), sgn_lift hστ (aE ζ a b)]
    exact apply_eq_sgn_mul_of_apply_sq_eq_sq τ a (hsq a q h.2.1)
  · rw [galE.eq_1, hστ (bE ζ a b), sgn_lift hστ (bE ζ a b)]
    exact apply_eq_sgn_mul_of_apply_sq_eq_sq τ b (hsq b d h.2.2.1)
  · rw [galE.eq_1]
    show hPart e ζ a b σ = hcl e u ↔ _
    rw [hPart_lift h hστ, hcl_eq_iff, ← trace_eq_iff_units h.1, hστ, ← apply_theta h.1 τ]
    exact Iff.rfl

theorem hostGaloisCore : HostFixed ∧ HostGalois ∧ HostGalSpec := ⟨hostFixed, hostGalois, hostGalSpec⟩

end Formalism.FrobeniusOrbits
