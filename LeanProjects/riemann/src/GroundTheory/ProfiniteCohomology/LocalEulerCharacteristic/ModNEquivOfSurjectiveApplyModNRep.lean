import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.UnitsLattice
import GroundTheory.LocalFields.NormalLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u

open GroundTheory.LocalField ValuativeRel IsLocalRing

section MonoidAlgebra

instance finite_monoidAlgebra {R M : Type*} [Semiring R] [Finite R] [Finite M] :
    Finite (MonoidAlgebra R M) :=
  Finite.of_injective (fun x : MonoidAlgebra R M ↦ (x.coeff : M → R))
    (fun _ _ h ↦ MonoidAlgebra.coeff_injective (DFunLike.coe_injective h))

end MonoidAlgebra

section ModNEquiv

variable {n : ℕ} {A X : Type*} [AddCommGroup A] [AddCommGroup X] [Module (ZMod n) X]

noncomputable def modNEquivOfSurjective (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n)) :
    ModN A n ≃ₗ[ZMod n] X :=
  LinearEquiv.ofBijective
    (((LinearMap.range (LinearMap.lsmul ℤ A n)).liftQ φ.toIntLinearMap
      fun a ha ↦ LinearMap.mem_ker.mpr ((hker a).mpr ha)).toAddMonoidHom.toZModLinearMap n)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (Submodule.Quotient.mk_eq_zero _).mpr ((hker a).mp hx),
    fun x ↦ by
      obtain ⟨a, ha⟩ := hs x
      exact ⟨Submodule.Quotient.mk a, ha⟩⟩

theorem modNEquivOfSurjective_mk (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n)) (a : A) :
    modNEquivOfSurjective φ hs hker (Submodule.Quotient.mk a) = φ a :=
  rfl

theorem modNEquivOfSurjective_apply_modNRep {Γ : Type*} [Group Γ] [DistribMulAction Γ A]
    (ρ : Representation (ZMod n) Γ X) (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n))
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) = ρ γ (φ a)) (γ : Γ) (x : ModN A n) :
    modNEquivOfSurjective φ hs hker (modNRep Γ A n γ x) =
      ρ γ (modNEquivOfSurjective φ hs hker x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk, modNEquivOfSurjective_mk, modNEquivOfSurjective_mk]
  exact hφ γ a

end ModNEquiv

section Int

abbrev trivialIntAction (Γ : Type*) [Monoid Γ] : DistribMulAction Γ (ULift.{u} ℤ) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

theorem finite_modN_uliftInt (l : ℕ) [NeZero l] : Finite (ModN (ULift.{u} ℤ) l) := by
  let e : ULift.{u} ℤ ≃+ ℤ := AddEquiv.ulift
  let b : Module.Basis Unit ℤ (ULift.{u} ℤ) :=
    (Module.Basis.singleton Unit ℤ).map e.symm.toIntLinearEquiv
  exact Finite.of_equiv _ (ModN.basis (n := l) b).equivFun.symm.toEquiv

theorem finite_torsN_uliftInt (l : ℕ) [NeZero l] : Finite (TorsN (ULift.{u} ℤ) l) := by
  have : Subsingleton (TorsN (ULift.{u} ℤ) l) := ⟨fun x y ↦ by
    have hx := (mem_ker_lsmul_iff l (x : ULift.{u} ℤ)).mp x.2
    have hy := (mem_ker_lsmul_iff l (y : ULift.{u} ℤ)).mp y.2
    have h0 : ∀ z : ULift.{u} ℤ, l • z = 0 → z = 0 := fun z hz ↦ by
      have h := congrArg (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ) hz
      rw [map_nsmul, map_zero, nsmul_eq_mul, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd h (by exact_mod_cast NeZero.ne l)
      · exact AddEquiv.ulift.injective (h.trans (map_zero _).symm)
    exact Subtype.ext ((h0 _ hx).trans (h0 _ hy).symm)⟩
  infer_instance

end Int

section Valuation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

noncomputable def ordHom : Additive Fˣ →+ ULift.{u} ℤ where
  toFun x := ULift.up (ord ((x.toMul : Fˣ) : F))
  map_zero' := by
    apply ULift.ext
    simp [ord]
  map_add' x y := by
    apply ULift.ext
    simp [ord_mul x.toMul.ne_zero y.toMul.ne_zero]

variable {F}

theorem ordHom_apply (x : Additive Fˣ) : ordHom F x = ULift.up (ord ((x.toMul : Fˣ) : F)) :=
  rfl

theorem ordHom_surjective : Function.Surjective (ordHom F) := by
  intro m
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  refine ⟨Additive.ofMul ((unitsEquivIntProd hϖ).symm (Multiplicative.ofAdd m.down, 1)), ?_⟩
  apply ULift.ext
  have := unitsEquivIntProd_fst hϖ ((unitsEquivIntProd hϖ).symm (Multiplicative.ofAdd m.down, 1))
  rw [MulEquiv.apply_symm_apply] at this
  rw [ordHom_apply]
  exact (Multiplicative.ofAdd.injective this).symm

theorem ordHom_exact : Function.Exact (unitsIncl F).toAdditive (ordHom F) := by
  intro x
  rw [ordHom_apply]
  constructor
  · intro h
    have h0 : ord ((x.toMul : Fˣ) : F) = 0 := congrArg ULift.down h
    have h1 : normalizedValuation F ((x.toMul : Fˣ) : F) = 1 := by
      rw [normalizedValuation_eq_exp_ord x.toMul.ne_zero, h0, neg_zero, WithZero.exp_zero]
    obtain ⟨u, hu⟩ := mem_range_unitsIncl_iff.mpr h1
    exact ⟨Additive.ofMul u, by simp [hu]⟩
  · rintro ⟨u, rfl⟩
    apply ULift.ext
    simp [ord_unit]

end Valuation

section Subgroup

theorem finite_quotient_range_toAdditive {G : Type*} [CommGroup G] (H : Subgroup G)
    [H.FiniteIndex] : Finite (Additive G ⧸ (H.subtype.toAdditive).range) := by
  have h : (H.subtype.toAdditive).range = H.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_range]
    change _ ↔ x.toMul ∈ H
    constructor
    · rintro ⟨a, rfl⟩
      exact a.toMul.2
    · intro hx
      exact ⟨Additive.ofMul ⟨x.toMul, hx⟩, rfl⟩
  rw [h]
  have : H.toAddSubgroup.FiniteIndex :=
    ⟨by rw [Subgroup.index_toAddSubgroup]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  infer_instance

theorem toAdditive_subtype_injective {G : Type*} [CommGroup G] (H : Subgroup G) :
    Function.Injective H.subtype.toAdditive :=
  fun _ _ h ↦ Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

theorem finite_modN_of_finite_cokernel {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}
    (f : B →+ A) [Finite (A ⧸ f.range)] [Finite (ModN B n)] : Finite (ModN A n) := by
  have hfh : Function.Exact f (QuotientAddGroup.mk' f.range) :=
    fun y ↦ by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  have : Finite (ModN (A ⧸ f.range) n) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  exact finite_modN_of_exact (QuotientAddGroup.mk'_surjective f.range) hfh

end Subgroup

section Torsion

theorem finite_torsN_of_torsion_trivial {A : Type*} [AddCommGroup A] {n : ℕ}
    (h : ∀ a : A, n • a = 0 → a = 0) : Finite (TorsN A n) :=
  have : Subsingleton (TorsN A n) := ⟨fun x y ↦ Subtype.ext
    ((h _ ((mem_ker_lsmul_iff n _).mp x.2)).trans (h _ ((mem_ker_lsmul_iff n _).mp y.2)).symm)⟩
  Finite.of_subsingleton

variable {F : Type*} [Field F] [ValuativeRel F]

theorem integer_subgroup_torsion {m : ℕ} (hm : (m : F) ≠ 0) (H : AddSubgroup 𝒪[F]) (a : H)
    (ha : m • a = 0) : a = 0 := by
  have hm' : (m : 𝒪[F]) ≠ 0 := fun h ↦ hm (by simpa using congrArg Subtype.val h)
  have h := congrArg (fun x : H ↦ (x : 𝒪[F])) ha
  simp only [AddSubgroup.coe_nsmul, nsmul_eq_mul, ZeroMemClass.coe_zero, mul_eq_zero, hm',
    false_or] at h
  exact Subtype.ext h

end Torsion

section Residue

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {p : ℕ}

noncomputable def modNIntegerEquiv : ModN 𝒪[E] p ≃ₗ[ℤ] 𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])} :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [mem_range_lsmul_iff, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    simp only [nsmul_eq_mul, mul_comm])).trans
    (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {(p : 𝒪[E])}))

variable [Fact p.Prime]

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in

theorem finrank_modN_integer {n : ℕ} (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) = p ^ n) :
    Finite (ModN 𝒪[E] p) ∧ Module.finrank (ZMod p) (ModN 𝒪[E] p) = n := by
  have hp := (Fact.out : p.Prime)
  have hcard : Nat.card (ModN 𝒪[E] p) = p ^ n := (Nat.card_congr modNIntegerEquiv.toEquiv).trans hn
  have hfin : Finite (ModN 𝒪[E] p) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite (ModN 𝒪[E] p)
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := ModN 𝒪[E] p)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
  exact (Nat.pow_right_injective hp.two_le h).symm

theorem exists_card_quotient_eq_pow (hp0 : (p : E) ≠ 0) :
    ∃ n, Nat.card (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) = p ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have hp' : (p : 𝒪[E]) ≠ 0 := fun h ↦ hp0 (by simpa using congrArg Subtype.val h)
  obtain ⟨m, ε, hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp' hπ
  have hfin : Finite (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) := by
    refine IsLocalRing.finite_quotient_iff.mpr ⟨m, fun x hx ↦ ?_⟩
    obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hπ).mp hx
    rw [Ideal.mem_span_singleton', hm]
    exact ⟨((ε⁻¹ : 𝒪[E]ˣ) : 𝒪[E]) * a, by
      have := ε.inv_mul
      linear_combination (π ^ m * a) * this⟩
  have hfin' : Finite (ModN 𝒪[E] p) := Finite.of_equiv _ modNIntegerEquiv.symm.toEquiv
  have := Fintype.ofFinite (ModN 𝒪[E] p)
  refine ⟨Module.finrank (ZMod p) (ModN 𝒪[E] p), ?_⟩
  rw [← Nat.card_congr modNIntegerEquiv.toEquiv, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

end Residue

section Filtration

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p e : ℕ} {ε : 𝒪[F]ˣ} (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe

theorem finite_modN_maxPow (k : ℕ) : Finite (ModN (maxPow F k) p) := by
  have hfin : Finite (𝒪[F] ⧸ 𝓂[F] ^ (k + e)) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k + e, le_rfl⟩
  let φ : maxPow F k →+ 𝒪[F] ⧸ 𝓂[F] ^ (k + e) :=
    (Ideal.Quotient.mk (𝓂[F] ^ (k + e))).toAddMonoidHom.comp (maxPow F k).subtype
  have hφ : ∀ a : maxPow F k, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ (maxPow F k) p) := by
    intro a
    rw [mem_range_lsmul_iff]
    change Ideal.Quotient.mk _ (a : 𝒪[F]) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_add_iff hϖ hpe]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simp [h])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, by simp⟩
  let L := (LinearMap.range (LinearMap.lsmul ℤ (maxPow F k) p)).liftQ φ.toIntLinearMap
    fun a ha ↦ LinearMap.mem_ker.mpr ((hφ a).mpr ha)
  refine Finite.of_injective L ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((hφ a).mp hx)

end Filtration

section Galois

variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]

theorem ord_algEquiv (σ : F ≃ₐ[E] F) (x : F) : ord (σ x) = ord x := by
  rw [ord, ord, (normalizedValuation_eq_iff).mpr (valuation_algEquiv_apply E F σ x)]

theorem ordHom_smul (σ : F ≃ₐ[E] F) (x : Additive Fˣ) : ordHom F (σ • x) = ordHom F x := by
  rw [ordHom_apply, ordHom_apply]
  exact congrArg ULift.up (ord_algEquiv σ ((x.toMul : Fˣ) : F))

theorem unitsIncl_toAdditive_smul (σ : F ≃ₐ[E] F) (a : Additive 𝒪[F]ˣ) :
    (unitsIncl F).toAdditive (σ • a) = σ • (unitsIncl F).toAdditive a :=
  congrArg Additive.ofMul (unitsIncl_smul σ a.toMul)

omit [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in

theorem finite_torsN_integerUnits (l : ℕ) [NeZero l] : Finite (TorsN (Additive 𝒪[F]ˣ) l) := by
  classical
  have hl : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  have key : ∀ x : TorsN (Additive 𝒪[F]ˣ) l,
      (((x : Additive 𝒪[F]ˣ).toMul : 𝒪[F]ˣ) : 𝒪[F]) ∈ Polynomial.nthRootsFinset l (1 : 𝒪[F]) := by
    intro x
    rw [Polynomial.mem_nthRootsFinset hl, ← Units.val_pow_eq_pow_val, ← toMul_nsmul,
      (mem_ker_lsmul_iff l _).mp x.2]
    rfl
  refine Finite.of_injective
    (fun x : TorsN (Additive 𝒪[F]ˣ) l ↦
      (⟨_, key x⟩ : (Polynomial.nthRootsFinset l (1 : 𝒪[F]) : Set 𝒪[F]))) ?_
  intro x y h
  exact Subtype.ext (Additive.toMul.injective (Units.ext (congrArg Subtype.val h)))

variable {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))

theorem g_units_eq_one_add [Finite (ModN (Additive 𝒪[F]ˣ) l)] :
    d.g (Additive Fˣ) = d.one + d.g (Additive 𝒪[F]ˣ) := by
  let := trivialIntAction.{u} (F ≃ₐ[E] F)
  have := finite_torsN_integerUnits (F := F) l
  have := finite_modN_uliftInt.{u} l
  have := finite_torsN_uliftInt.{u} l
  have hinj : Function.Injective (unitsIncl F).toAdditive :=
    fun _ _ h ↦ Additive.toMul.injective (unitsIncl_injective (Additive.ofMul.injective h))
  rw [d.g_add (unitsIncl F).toAdditive (ordHom F) unitsIncl_toAdditive_smul
      (fun σ x ↦ ordHom_smul σ x) hinj ordHom_exact ordHom_surjective,
    d.g_of_trivial_int (ULift.{u} ℤ) (fun _ _ ↦ rfl) AddEquiv.ulift, add_comm]

attribute [local instance] integerAction unitFiltrationAction

attribute [local instance] maxPowAction normalSubAction

omit [FiniteDimensional E F] in

theorem valuation_le_of_mem_maxPow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {k : ℕ} {x : 𝒪[F]}
    (hx : x ∈ 𝓂[F] ^ k) : valuation F (x : F) ≤ valuation F (ϖ : F) ^ k := by
  obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hx
  rw [Subring.coe_mul, map_mul, SubmonoidClass.coe_pow, map_pow]
  exact mul_le_of_le_one_right' a.2

theorem exists_maxPow_le_normalSub [IsGalois E F] {θ : F}
    (hθ : LinearIndependent E fun σ : F ≃ₐ[E] F ↦ σ θ) :
    ∃ j, ∀ k ≥ j, maxPow F k ≤ normalSub E θ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hopen := isOpen_normalLattice π θ hπ hθ 0
  rw [normalLattice_zero_eq] at hopen
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp
    (hopen.mem_nhds (Submodule.zero_mem _))
  obtain ⟨j, -, hj⟩ := exists_pow_lt hϖ γ.ne_zero
  refine ⟨j, fun k hk x hx ↦ mem_normalSub.mpr (hγ ?_)⟩
  have h1 : valuation F (ϖ : F) ≤ 1 := ϖ.2
  calc valuation F (x : F) ≤ valuation F (ϖ : F) ^ k := valuation_le_of_mem_maxPow hϖ hx
    _ ≤ valuation F (ϖ : F) ^ j := pow_le_pow_right_of_le_one' h1 hk
    _ < γ := hj

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension E F]
  [FiniteDimensional E F] in

theorem finite_quotient_maxPow {θ : F} {k : ℕ} (hle : maxPow F k ≤ normalSub E θ) :
    Finite (normalSub E θ ⧸ (AddSubgroup.inclusion hle).range) := by
  have hr : (AddSubgroup.inclusion hle).range = (maxPow F k).addSubgroupOf (normalSub E θ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hfin : Finite (𝒪[F] ⧸ maxPow F k) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k, le_rfl⟩
  have hidx : (maxPow F k).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hrel : (maxPow F k).relIndex (normalSub E θ) ≠ 0 :=
    fun h ↦ hidx (Nat.eq_zero_of_zero_dvd (h ▸ AddSubgroup.relIndex_dvd_index_of_le hle))
  rw [hr]
  have : ((maxPow F k).addSubgroupOf (normalSub E θ)).FiniteIndex := ⟨hrel⟩
  infer_instance

end Galois

section LemmaA

variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [IsGalois E F]
  {l : ℕ} [Fact l.Prime] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))

attribute [local instance] integerAction unitFiltrationAction maxPowAction normalSubAction

theorem g_integerUnits_eq (hl : (l : F) ≠ 0) {n : ℕ}
    (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(l : 𝒪[E])}) = l ^ n) :
    Finite (ModN (Additive 𝒪[F]ˣ) l) ∧
      d.g (Additive 𝒪[F]ˣ) = n * d.toFun (MonoidAlgebra (ZMod l) (F ≃ₐ[E] F))
        (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) := by
  have hlp : l.Prime := Fact.out
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hl' : (l : 𝒪[F]) ≠ 0 := fun h ↦ hl (by simpa using congrArg Subtype.val h)
  obtain ⟨e, ε, hpe⟩ : ∃ (e : ℕ) (ε : 𝒪[F]ˣ), (l : 𝒪[F]) = ϖ ^ e * ε := by
    obtain ⟨e, ε, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl' hϖ
    exact ⟨e, ε, by rw [h, mul_comm]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨θ, hθ, hθO⟩ := exists_normalBasis_integer (K := E) (L := F) hπ
  obtain ⟨j, hj⟩ := exists_maxPow_le_normalSub hθ
  have hk : e + 1 ≤ max j (e + 1) := le_max_right _ _
  have hle : maxPow F (max j (e + 1)) ≤ normalSub E θ := hj _ (le_max_left _ _)
  set k := max j (e + 1)
  obtain ⟨hfinE, hrank⟩ := finrank_modN_integer (E := E) hn
  let b : Module.Basis (Fin n) (ZMod l) (ModN 𝒪[E] l) := Module.finBasisOfFinrankEq _ _ hrank

  set U := unitFiltration F k
  have hUt : ∀ a : Additive U, l • a = 0 → a = 0 := by
    intro a ha
    apply Additive.toMul.injective
    have h1 : (a.toMul : 𝒪[F]ˣ) ^ l = 1 := by
      have := congrArg (fun b : Additive U ↦ ((b.toMul : U) : 𝒪[F]ˣ)) ha
      simpa using this
    exact Subtype.ext (eq_one_of_mem_unitFiltration_of_pow_eq_one hϖ hlp hpe hk a.toMul.2 h1)
  let e1 := modNEquivOfSurjective (unitToModN hϖ hpe (Nat.le_of_succ_le hk))
    (unitToModN_surjective hϖ hpe hk) (unitToModN_eq_zero_iff hϖ hpe hlp hk)
  have he1 := modNEquivOfSurjective_apply_modNRep (modNRep (F ≃ₐ[E] F) (maxPow F k) l)
    (unitToModN hϖ hpe (Nat.le_of_succ_le hk)) (unitToModN_surjective hϖ hpe hk)
    (unitToModN_eq_zero_iff hϖ hpe hlp hk) (unitToModN_smul ϖ hϖ hpe _)
  have := finite_modN_maxPow hϖ hpe k
  have : Finite (ModN (Additive U) l) := Finite.of_equiv _ e1.symm.toEquiv
  have := finite_torsN_of_torsion_trivial hUt
  have hPt : ∀ a : maxPow F k, l • a = 0 → a = 0 := integer_subgroup_torsion hl _
  have := finite_torsN_of_torsion_trivial hPt

  let N := normalSubEquiv hθ hθO
  let φ : normalSub E θ →+ (Fin n → MonoidAlgebra (ZMod l) (F ≃ₐ[E] F)) :=
    (coeffToRegular b).comp N.symm.toAddMonoidHom
  have hφs : Function.Surjective φ :=
    (coeffToRegular_surjective (F ≃ₐ[E] F) b).comp N.symm.surjective
  have hφk : ∀ t, φ t = 0 ↔ t ∈ LinearMap.range (LinearMap.lsmul ℤ (normalSub E θ) l) := by
    intro t
    change coeffToRegular b (N.symm t) = 0 ↔ _
    rw [coeffToRegular_eq_zero_iff, mem_range_lsmul_iff, mem_range_lsmul_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨N y, by rw [← map_nsmul, hy, AddEquiv.apply_symm_apply]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨N.symm y, by rw [map_nsmul]⟩
  have hφγ : ∀ (σ : F ≃ₐ[E] F) (t : normalSub E θ), φ (σ • t) =
      piRep (Fin n) (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) σ (φ t) := by
    intro σ t
    obtain ⟨c, rfl⟩ := N.surjective t
    change coeffToRegular b (N.symm (σ • N c)) = piRep (Fin n)
      (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) σ (coeffToRegular b (N.symm (N c)))
    rw [AddEquiv.symm_apply_apply, normalSubEquiv_apply, smul_normalSubOfCoeff,
      ← normalSubEquiv_apply hθ, AddEquiv.symm_apply_apply, coeffToRegular_perm]
  let e2 := modNEquivOfSurjective φ hφs hφk
  have he2 := modNEquivOfSurjective_apply_modNRep _ φ hφs hφk hφγ
  have : Finite (ModN (normalSub E θ) l) := Finite.of_equiv _ e2.symm.toEquiv
  have hTt : ∀ a : normalSub E θ, l • a = 0 → a = 0 := integer_subgroup_torsion hl _
  have := finite_quotient_maxPow hle
  have := finite_quotient_range_toAdditive U
  refine ⟨finite_modN_of_finite_cokernel U.subtype.toAdditive, ?_⟩
  rw [d.g_eq_of_finite_cokernel U.subtype.toAdditive (fun _ _ ↦ rfl)
      (toAdditive_subtype_injective U),
    d.g_eq_of_torsion_trivial (Additive U) hUt, d.toFun_congr _ _ e1 he1,
    ← d.g_eq_of_torsion_trivial (maxPow F k) hPt,
    ← d.g_eq_of_finite_cokernel (AddSubgroup.inclusion hle) (fun _ _ ↦ rfl)
      (AddSubgroup.inclusion_injective hle),
    d.g_eq_of_torsion_trivial (normalSub E θ) hTt, d.toFun_congr _ _ e2 he2, d.toFun_pi]

theorem g_units_eq (hl : (l : E) ≠ 0) {n : ℕ}
    (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(l : 𝒪[E])}) = l ^ n) :
    d.g (Additive Fˣ) = d.one + n * d.toFun (MonoidAlgebra (ZMod l) (F ≃ₐ[E] F))
      (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) := by
  have hlF : (l : F) ≠ 0 := by
    rw [← map_natCast (algebraMap E F)]
    exact (map_ne_zero _).mpr hl
  obtain ⟨hfin, hg⟩ := g_integerUnits_eq d hlF hn
  rw [g_units_eq_one_add d, hg]

end LemmaA

end GroundTheory.ProfCoh
