import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation

namespace GroundTheory.LocalField.Abstract

section Unramified

variable {G : Type*} [Group G] (d : G →* Multiplicative ℤ̂)

def IsUnramified (K L : Subgroup G) : Prop :=
  relRamificationIndex d K L = 1

variable {d}

theorem isUnramified_iff {K L : Subgroup G} : IsUnramified d K L ↔ K ⊓ d.ker ≤ L := by
  rw [IsUnramified, relRamificationIndex, Subgroup.relIndex_eq_one, inf_comm]

theorem relIndex_eq_relInertiaDegree {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    L.relIndex K = relInertiaDegree d K L := by
  rw [relIndex_eq_mul (d := d) hLK, (isUnramified_iff.2 hu : relRamificationIndex d K L = 1), one_mul]

theorem mem_iff_map_mem_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L)
    {σ : G} (hσ : σ ∈ K) : σ ∈ L ↔ d σ ∈ L.map d := by
  refine ⟨fun h => ⟨σ, h, rfl⟩, ?_⟩
  rintro ⟨τ, hτ, hτσ⟩
  have h : τ⁻¹ * σ ∈ L := hu (Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem (hLK hτ)) hσ,
    MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hτσ, inv_mul_cancel])⟩)
  simpa using L.mul_mem hτ h

theorem normal_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    (L.subgroupOf K).Normal := by
  have h : L.subgroupOf K = (L.map d).comap (d.comp K.subtype) := by
    ext σ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact mem_iff_map_mem_of_unramified hLK hu σ.2
  rw [h]
  exact Subgroup.Normal.comap inferInstance _

end Unramified

namespace ClassFieldData

open ProfiniteInteger

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)

section Frobenius

variable {K L : OpenSubgroup G}

theorem exists_pow_mul_mem_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) (τ : (K : Subgroup G)) :
    ∃ m : ℕ, ((φ ^ m)⁻¹ * τ : G) ∈ (L : Subgroup G) := by
  set n : ℕ+ := ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩
  set x : ℤ̂ := Multiplicative.toAdd (D.relDeg K τ)
  set m : ℕ := (proj n x).val
  have hx : x - (m : ℤ̂) ∈ multiples n := by
    rw [← proj_eq_zero_iff, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := mem_multiples.1 hx
  obtain ⟨ρ, hρ, hρw⟩ := (D.mem_map_relDeg_iff hLK).2 ⟨Multiplicative.ofAdd w, rfl⟩
  refine ⟨m, ?_⟩
  have hdeg : D.relDeg K (ρ⁻¹ * ((φ ^ m)⁻¹ * τ)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, hφ, hρw]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_one]
    have hw' : relInertiaDegree D.deg K L • w = x - m := hw.symm
    rw [hw', nsmul_one]
    abel
  have hker : ((ρ⁻¹ * ((φ ^ m)⁻¹ * τ) : (K : Subgroup G)) : G) ∈ (K : Subgroup G) ⊓ D.deg.ker := by
    refine Subgroup.mem_inf.2 ⟨Subtype.coe_prop _, MonoidHom.mem_ker.2 ?_⟩
    rw [← relDeg_pow, hdeg, one_pow]
  have h := (L : Subgroup G).mul_mem (Subgroup.mem_subgroupOf.1 hρ) (hu hker)
  simpa using h

theorem zpowers_eq_top_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal]
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) :
    Subgroup.zpowers ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) = ⊤ := by
  refine eq_top_iff.2 fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H τ =>
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ τ
    refine ⟨m, ?_⟩
    change ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) ^ (m : ℤ) = τ
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hm

theorem isCyclic_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K (Multiplicative.ofAdd 1)
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, D.zpowers_eq_top_of_unramified hLK hu hφ⟩

end Frobenius

section TateZero

variable {K L : OpenSubgroup G}

noncomputable def valuationMod (K : OpenSubgroup G) (n : ℕ+) :
    fixedModule A (K : Subgroup G) →* Multiplicative (ZMod n) :=
  (AddMonoidHom.toMultiplicative (proj n).toAddMonoidHom).comp (D.valuation K)

theorem valuationMod_apply (K : OpenSubgroup G) (n : ℕ+) (a : fixedModule A (K : Subgroup G)) :
    D.valuationMod K n a = Multiplicative.ofAdd (proj n (Multiplicative.toAdd (D.valuation K a))) :=
  rfl

theorem valuationMod_surjective (K : OpenSubgroup G) (n : ℕ+) :
    Function.Surjective (D.valuationMod K n) := by
  intro z
  have h : Multiplicative.ofAdd ((Multiplicative.toAdd z).val : ℤ̂) ∈ (D.valuation K).range := by
    rw [range_valuation]
    exact_mod_cast D.intCast_mem_range_val ((Multiplicative.toAdd z).val : ℤ)
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [valuationMod_apply, ha, toAdd_ofAdd, map_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd]

noncomputable def relInertiaDegreePNat (hLK : L ≤ K) : ℕ+ :=
  ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩

@[simp] theorem coe_relInertiaDegreePNat (hLK : L ≤ K) :
    (D.relInertiaDegreePNat hLK : ℕ) = relInertiaDegree D.deg K L :=
  rfl

theorem range_norm_le_ker_valuationMod (hLK : L ≤ K) :
    (norm A (K : Subgroup G) (L : Subgroup G)).range ≤
      (D.valuationMod K (D.relInertiaDegreePNat hLK)).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, valuationMod_apply, D.valuation_norm hLK, toAdd_pow, map_nsmul,
    nsmul_eq_mul]
  change Multiplicative.ofAdd (((D.relInertiaDegreePNat hLK : ℕ) : ZMod (D.relInertiaDegreePNat hLK)) *
    _) = 1
  rw [ZMod.natCast_self, zero_mul, ofAdd_zero]

noncomputable def tateZeroVal (hLK : L ≤ K) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      Multiplicative (ZMod (D.relInertiaDegreePNat hLK)) :=
  QuotientGroup.lift _ (D.valuationMod K (D.relInertiaDegreePNat hLK))
    (D.range_norm_le_ker_valuationMod hLK)

theorem tateZeroVal_mk (hLK : L ≤ K) (a : fixedModule A (K : Subgroup G)) :
    D.tateZeroVal hLK (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      D.valuationMod K (D.relInertiaDegreePNat hLK) a :=
  rfl

theorem tateZeroVal_surjective (hLK : L ≤ K) : Function.Surjective (D.tateZeroVal hLK) := by
  intro z
  obtain ⟨a, ha⟩ := D.valuationMod_surjective K (D.relInertiaDegreePNat hLK) z
  exact ⟨a, ha⟩

theorem tateZeroVal_bijective (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) : Function.Bijective (D.tateZeroVal hLK) := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcyc := D.isCyclic_of_unramified hLK hu
  have hcard := (hax K L hLK hcyc).1
  rw [relIndex_eq_relInertiaDegree hLK hu] at hcard
  have : Finite (tateZero A (K : Subgroup G) (L : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact D.relInertiaDegree_ne_zero hLK)
  refine (D.tateZeroVal_surjective hLK).bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, coe_relInertiaDegreePNat]

noncomputable def tateZeroEquiv (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    tateZero A (K : Subgroup G) (L : Subgroup G) ≃*
      Multiplicative (ZMod ((L : Subgroup G).relIndex K)) :=
  (MulEquiv.ofBijective _ (D.tateZeroVal_bijective hax hLK hu)).trans
    (AddEquiv.toMultiplicative
      (ZMod.ringEquivCongr (m := (D.relInertiaDegreePNat hLK : ℕ))
        (relIndex_eq_relInertiaDegree (d := D.deg) hLK hu).symm).toAddEquiv)

end TateZero

section Units

variable {K L : OpenSubgroup G}

theorem norm_mem_units (hLK : L ≤ K) {a : fixedModule A (L : Subgroup G)} (ha : a ∈ D.units L) :
    norm A (K : Subgroup G) (L : Subgroup G) a ∈ D.units K := by
  rw [D.mem_units, D.valuation_norm hLK, D.mem_units.1 ha, one_pow]

theorem units_eq_map_norm (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    D.units K = (D.units L).map (norm A (K : Subgroup G) (L : Subgroup G)) := by
  refine le_antisymm ?_ ?_
  · intro u hU
    have h1 : D.tateZeroVal hLK (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 := by
      rw [tateZeroVal_mk, valuationMod_apply, D.mem_units.1 hU, toAdd_one, map_zero, ofAdd_zero]
    have h2 : (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 :=
      (D.tateZeroVal_bijective hax hLK hu).1 (by rw [h1, map_one])
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff u).1 h2
    refine ⟨x, ?_, hx⟩
    show x ∈ D.units L
    rw [D.mem_units]
    have h3 := D.valuation_norm hLK x
    rw [hx, D.mem_units.1 hU] at h3
    exact (ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1
      (by rw [one_pow]; exact h3.symm)
  · rintro _ ⟨x, hx, rfl⟩
    exact D.norm_mem_units hLK hx

theorem exists_eq_smul_div_of_mem_augmentation (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {x : A}
    (hx : x ∈ augmentation A (K : Subgroup G) (L : Subgroup G)) :
    ∃ b ∈ fixedModule A (L : Subgroup G), x = (φ : G) • b / b := by
  have := normal_of_unramified (d := D.deg) hLK hu

  let S : Subgroup A :=
    { carrier := {y | ∃ b ∈ fixedModule A (L : Subgroup G), y = (φ : G) • b / b}
      one_mem' := ⟨1, Subgroup.one_mem _, by rw [smul_one, div_one]⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b * c, Subgroup.mul_mem _ hb hc, by rw [smul_mul', mul_div_mul_comm]⟩
      inv_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, Subgroup.inv_mem _ hb, by rw [smul_inv', inv_div_inv, inv_div]⟩ }

  let T : Subgroup (K : Subgroup G) :=
    { carrier := {g | ∀ a ∈ fixedModule A (L : Subgroup G), (g : G) • a / a ∈ S}
      one_mem' := fun a _ => by
        rw [OneMemClass.coe_one, one_smul, div_self']
        exact S.one_mem
      mul_mem' := by
        intro g h hg hh a ha
        have hha : (h : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK h.2 ha
        have e : ((g * h : (K : Subgroup G)) : G) • a / a =
            ((g : G) • ((h : G) • a) / ((h : G) • a)) * ((h : G) • a / a) := by
          rw [Subgroup.coe_mul, mul_smul]
          simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact S.mul_mem (hg _ hha) (hh a ha)
      inv_mem' := by
        intro g hg a ha
        have hga : ((g⁻¹ : (K : Subgroup G)) : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK (g⁻¹).2 ha
        have e : ((g⁻¹ : (K : Subgroup G)) : G) • a / a =
            ((g : G) • (((g⁻¹ : (K : Subgroup G)) : G) • a) / (((g⁻¹ : (K : Subgroup G)) : G) • a))⁻¹ := by
          rw [smul_smul, InvMemClass.coe_inv, mul_inv_cancel, one_smul, inv_div]
        rw [e]
        exact S.inv_mem (hg _ hga) }
  have hφT : φ ∈ T := fun a ha => ⟨a, ha, rfl⟩
  have hLT : ∀ ρ : (K : Subgroup G), (ρ : G) ∈ (L : Subgroup G) → ρ ∈ T := fun ρ hρ a ha => by
    rw [ha ρ hρ, div_self']
    exact S.one_mem
  have hTop : ∀ g : (K : Subgroup G), g ∈ T := by
    intro g
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ g
    have hg : g = φ ^ m * ((φ ^ m)⁻¹ * g) := by group
    rw [hg]
    exact T.mul_mem (T.pow_mem hφT m) (hLT _ (by simpa using hm))
  have hle : augmentation A (K : Subgroup G) (L : Subgroup G) ≤ S := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, a, ha, rfl⟩
    exact hTop ⟨g, hg⟩ a ha
  exact hle hx

theorem exists_units_eq_smul_div (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) {φ : (K : Subgroup G)}
    (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {u : fixedModule A (L : Subgroup G)}
    (hN : norm A (K : Subgroup G) (L : Subgroup G) u = 1) :
    ∃ ε ∈ D.units L, (u : A) = (φ : G) • (ε : A) / ε := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcard := (hax K L hLK (D.isCyclic_of_unramified hLK hu)).2
  have hsub := (Nat.card_eq_one_iff_unique.1 hcard).1

  have haug : (u : A) ∈ augmentation A (K : Subgroup G) (L : Subgroup G) := by
    have h := (QuotientGroup.eq_one_iff
      (N := (augmentation A (K : Subgroup G) (L : Subgroup G)).comap
        ((fixedModule A (L : Subgroup G)).subtype.comp
          (norm A (K : Subgroup G) (L : Subgroup G)).ker.subtype))
      (⟨u, hN⟩ : (norm A (K : Subgroup G) (L : Subgroup G)).ker)).1 (Subsingleton.elim _ _)
    exact h
  obtain ⟨b, hb, hub⟩ := D.exists_eq_smul_div_of_mem_augmentation hLK hu hφ haug

  have hval : D.valuation L ⟨b, hb⟩ ∈ (D.valuation K).range := by
    rw [range_valuation, ← D.range_valuation L]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := hval
  have he : relRamificationIndex D.deg K L = 1 := isUnramified_iff.2 hu
  refine ⟨⟨b, hb⟩ / ⟨c, fixedModule_anti hLK c.2⟩, ?_, ?_⟩
  · rw [D.mem_units, map_div, D.valuation_of_mem hLK c.2, he, pow_one]
    change D.valuation L ⟨b, hb⟩ / D.valuation K c = 1
    rw [hc, div_self']
  · have hφc : (φ : G) • (c : A) = c := c.2 φ φ.2
    change (u : A) = (φ : G) • ((b : A) / c) / (b / c)
    rw [smul_div', hφc, div_div_div_cancel_right, hub]

end Units

end ClassFieldData

end GroundTheory.LocalField.Abstract
