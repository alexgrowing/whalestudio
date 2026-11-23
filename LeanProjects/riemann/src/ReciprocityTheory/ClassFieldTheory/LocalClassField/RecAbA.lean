import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

noncomputable section

theorem qz_mk_eq_zero_iff (q : ℚ) : (QuotientAddGroup.mk q : QZ) = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  rw [QuotientAddGroup.eq_zero_iff]; rfl

theorem qz_nsmul_mk (l : ℕ) (q : ℚ) : l • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((l : ℚ) * q) := by
  rw [← nsmul_eq_mul]; rfl

theorem qz_zsmul_mk (l : ℤ) (q : ℚ) : l • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((l : ℚ) * q) := by
  rw [← zsmul_eq_mul]; rfl

theorem qz_exists_zsmul (n : ℕ) (hn : n ≠ 0) (x : QZ) (hx : n • x = 0) :
    ∃ k : ℤ, x = k • (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [qz_nsmul_mk, qz_mk_eq_zero_iff] at hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  rw [qz_zsmul_mk, hk]
  have : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  congr 1
  field_simp

theorem qz_nsmul_inv_eq_zero_iff (n : ℕ) (hn : n ≠ 0) (l : ℕ) :
    l • (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) = 0 ↔ n ∣ l := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [qz_nsmul_mk, qz_mk_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have h : ((k * n : ℤ) : ℚ) = ((l : ℤ) : ℚ) := by
      push_cast
      rw [hk]
      field_simp
    have h' : k * n = (l : ℤ) := Int.cast_injective h
    exact Int.natCast_dvd_natCast.1 ⟨k, by rw [← h', mul_comm]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    field_simp

scoped instance hasEnoughRootsOfUnity_QZ (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (Multiplicative QZ) n where
  prim := ⟨Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n)),
    { pow_eq_one := by
        rw [← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]; rfl
      dvd_of_pow_eq_one := fun l hl => by
        rw [← ofAdd_nsmul] at hl
        exact (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) l).1 (Multiplicative.ofAdd.injective hl) }⟩
  cyc := by
    have h0 : (toUnits (Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ))) ∈
        rootsOfUnity n (Multiplicative QZ) := by
      rw [mem_rootsOfUnity, ← map_pow, ← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]
      exact map_one _
    refine ⟨⟨⟨_, h0⟩, fun x => ?_⟩⟩
    have hx : n • Multiplicative.toAdd (x.1 : Multiplicative QZ) = 0 := by
      have := x.2
      rw [mem_rootsOfUnity] at this
      have h2 := congrArg (fun u : (Multiplicative QZ)ˣ => Multiplicative.toAdd (u : Multiplicative QZ)) this
      simpa using h2
    obtain ⟨k, hk⟩ := qz_exists_zsmul n (NeZero.ne n) _ hx
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply Multiplicative.toAdd.injective
    rw [hk]
    simp

section fin

variable (A : Type) [AddCommGroup A] [Finite A]

def homEquivUnits : (A →+ QZ) ≃ (Multiplicative A →* (Multiplicative QZ)ˣ) :=
  AddMonoidHom.toMultiplicative.trans (toUnits (G := Multiplicative QZ)).monoidHomCongrRight.toEquiv

theorem homEquivUnits_apply (χ : A →+ QZ) (a : A) :
    Multiplicative.toAdd ((homEquivUnits A χ (Multiplicative.ofAdd a) : (Multiplicative QZ)ˣ) : Multiplicative QZ) = χ a := rfl

scoped instance : NeZero (Monoid.exponent (Multiplicative A)) := ⟨Monoid.exponent_ne_zero_of_finite⟩

theorem card_hom_QZ : Nat.card (A →+ QZ) = Nat.card A := by
  rw [Nat.card_congr (homEquivUnits A),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative A) (Multiplicative QZ)]
  rfl

scoped instance finite_hom_QZ : Finite (A →+ QZ) :=
  Nat.finite_of_card_ne_zero (by rw [card_hom_QZ]; exact Nat.card_pos.ne')

variable {A}

theorem exists_hom_QZ_ne_zero {a : A} (ha : a ≠ 0) : ∃ χ : A →+ QZ, χ a ≠ 0 := by
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative A) (Multiplicative QZ)
    (a := Multiplicative.ofAdd a) (fun h => ha (Multiplicative.ofAdd.injective h))
  refine ⟨(homEquivUnits A).symm φ, fun h => hφ ?_⟩
  rw [← homEquivUnits_apply, Equiv.apply_symm_apply] at h
  exact Units.ext (Multiplicative.toAdd.injective h)

theorem exists_eval_QZ (f : (A →+ QZ) →+ QZ) : ∃ a : A, ∀ χ : A →+ QZ, χ a = f χ := by
  let ev : A →+ ((A →+ QZ) →+ QZ) := AddMonoidHom.flip (AddMonoidHom.id (A →+ QZ))
  have hinj : Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    obtain ⟨χ, hχ⟩ := exists_hom_QZ_ne_zero h
    exact hχ (DFunLike.congr_fun ha χ)
  have hbij : Bijective ev := hinj.bijective_of_nat_card_le (by rw [card_hom_QZ, card_hom_QZ])
  obtain ⟨a, ha⟩ := hbij.2 f
  exact ⟨a, fun χ => DFunLike.congr_fun ha χ⟩

end fin

section top

variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))

def pullChar : (A →+ QZ) →+ charGrp G where
  toFun ψ := ⟨ψ.comp π, hc.comp ψ⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pullChar_apply (ψ : A →+ QZ) (g : G) : (pullChar π hc ψ).1 (Additive.ofMul g) = ψ (π (Additive.ofMul g)) := rfl

variable {π}

theorem pullChar_injective (hπ : Surjective π) : Injective (pullChar π hc) := by
  intro ψ ψ' h
  ext a
  obtain ⟨g, rfl⟩ := hπ a
  exact DFunLike.congr_fun (congrArg Subtype.val h) g

theorem exists_pullChar_eq (hπ : Surjective π) (χ : charGrp G)
    (h : ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) : ∃ ψ, pullChar π hc ψ = χ := by
  refine ⟨π.liftOfSurjective hπ ⟨χ.1, fun g hg => h (Additive.toMul g) hg⟩, Subtype.ext ?_⟩
  exact AddMonoidHom.liftOfRightInverse_comp _ _ _ _

include hc

theorem exists_character_ne_zero_of_quotient [Finite A] (g : G) (hg : π (Additive.ofMul g) ≠ 0) :
    ∃ χ : charGrp G, (∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) ∧ χ.1 (Additive.ofMul g) ≠ 0 := by
  obtain ⟨ψ, hψ⟩ := exists_hom_QZ_ne_zero hg
  exact ⟨pullChar π hc ψ, fun g hg => by rw [pullChar_apply, hg, map_zero], hψ⟩

theorem card_characters_of_finite_quotient [Finite A] (hπ : Surjective π) :
    Nat.card {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0} = Nat.card A := by
  rw [← card_hom_QZ A]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun ψ : A →+ QZ => (⟨pullChar π hc ψ, fun g hg => by rw [pullChar_apply, hg, map_zero]⟩ :
      {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0})) ⟨?_, ?_⟩)).symm
  · intro ψ ψ' h
    exact pullChar_injective hc hπ (congrArg Subtype.val h)
  · rintro ⟨χ, hχ⟩
    obtain ⟨ψ, hψ⟩ := exists_pullChar_eq hc hπ χ hχ
    exact ⟨ψ, Subtype.ext hψ⟩

theorem exists_element_evaluating_characters [Finite A] (hπ : Surjective π) (f : charGrp G →+ QZ) :
    ∃ g : G, ∀ χ : charGrp G, (∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) →
      χ.1 (Additive.ofMul g) = f χ := by
  obtain ⟨a, ha⟩ := exists_eval_QZ (f.comp (pullChar π hc))
  obtain ⟨g, rfl⟩ := hπ a
  refine ⟨Additive.toMul g, fun χ hχ => ?_⟩
  obtain ⟨ψ, rfl⟩ := exists_pullChar_eq hc hπ χ hχ
  exact ha ψ

end top

section quot

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]

abbrev quotAddCommGroup (h : commutator G ≤ H) : AddCommGroup (Additive (G ⧸ H)) :=
  { (inferInstance : AddGroup (Additive (G ⧸ H))) with
    add_comm := fun a b => by
      have := (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := H)).2 h
      exact congrArg Additive.ofMul (this.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }

end quot

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
