import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E]

theorem exists_finite_units_mod_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set (𝓞 E)ˣ, S.Finite ∧ ∀ u : (𝓞 E)ˣ, ∃ s ∈ S, ∃ w : (𝓞 E)ˣ, u = s * w ^ h := by
  have : Group.FG (𝓞 E)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 E)ˣ h0
  have : Finite ((𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (Quotient.out : (𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range → (𝓞 E)ˣ),
    @Set.finite_range _ _ _ this, fun u => ?_⟩
  obtain ⟨⟨_, w, rfl⟩, hw⟩ := QuotientGroup.mk_out_eq_mul (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range u
  refine ⟨_, ⟨(u : (𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range), rfl⟩, w⁻¹, ?_⟩
  rw [hw]
  simp

theorem exists_finite_mod_units_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set E, S.Finite ∧ ∀ y ∈ powIdealElts E h, ∃ s ∈ S, ∃ (x : E) (u : (𝓞 E)ˣ),
      y = x ^ h * s * ((u : 𝓞 E) : E) := by
  classical
  have key : ∀ y : powIdealElts E h, ∃ 𝔞 : (FractionalIdeal (𝓞 E)⁰ E)ˣ,
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (y : E) = (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ^ h := by
    rintro ⟨y, hy, 𝔞, ha⟩
    refine ⟨Units.mk0 𝔞 ?_, ha⟩
    rintro rfl
    rw [zero_pow h0, FractionalIdeal.spanSingleton_eq_zero_iff] at ha
    exact hy ha
  choose A hA using key
  let c : powIdealElts E h → ClassGroup (𝓞 E) := fun y => ClassGroup.mk E (A y)
  let r : Set.range c → E := fun t => (t.2.choose : E)
  refine ⟨Set.range r, Set.finite_range _, fun y hy => ⟨_, ⟨⟨c ⟨y, hy⟩, _, rfl⟩, rfl⟩, ?_⟩⟩
  have ht : c ⟨y, hy⟩ ∈ Set.range c := ⟨_, rfl⟩
  have h1 : c ht.choose = c ⟨y, hy⟩ := ht.choose_spec
  change ∃ (x : E) (u : (𝓞 E)ˣ), y = x ^ h * (ht.choose : E) * ((u : 𝓞 E) : E)
  generalize ht.choose = s at h1
  have h2 : ClassGroup.mk E (A ⟨y, hy⟩ * (A s)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact h1.symm
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h2)
  have h3 : ((A ⟨y, hy⟩ : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ x * A s := by
    rw [← hx, ← Units.val_mul, inv_mul_cancel_right]
  have h4 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x ^ h * s) = FractionalIdeal.spanSingleton (𝓞 E)⁰ y := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow, hA s, ← mul_pow,
      ← h3]
    exact (hA ⟨y, hy⟩).symm
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h4
  refine ⟨x, u, ?_⟩
  rw [← hu, Units.smul_def, Algebra.smul_def, mul_comm]

theorem exists_finite_mod_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set E, S.Finite ∧ ∀ y ∈ powIdealElts E h, ∃ s ∈ S, ∃ x : E, y = x ^ h * s := by
  obtain ⟨S, hS, H⟩ := exists_finite_mod_units_pow (E := E) h0
  obtain ⟨T, hT, H'⟩ := exists_finite_units_mod_pow (E := E) h0
  refine ⟨Set.image2 (fun s (t : (𝓞 E)ˣ) => s * ((t : 𝓞 E) : E)) S T, hS.image2 _ hT, fun y hy => ?_⟩
  obtain ⟨s, hs, x, u, rfl⟩ := H y hy
  obtain ⟨t, ht, w, rfl⟩ := H' u
  refine ⟨_, ⟨s, hs, t, ht, rfl⟩, x * ((w : 𝓞 E) : E), ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, RingOfIntegers.coe_eq_algebraMap]
  ring

theorem finiteDimensional_kummerField (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ) (h0 : h ≠ 0) :
    FiniteDimensional ℚ (kummerField φ h) := by
  obtain ⟨S, hS, H⟩ := exists_finite_mod_pow (E := E) h0
  let R : Set ℂ := ⋃ s ∈ insert 1 S, {z | z ^ h = φ s}
  have hR : R.Finite := (hS.insert 1).biUnion fun s _ =>
    ((Polynomial.nthRoots h (φ s)).finite_toSet).subset fun z hz =>
      (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero h0)).2 hz
  have : Finite R := hR
  have h1 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ R) := by
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    obtain ⟨s, -, hs⟩ := Set.mem_iUnion₂.1 hz
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero h0) ?_
    rw [show z ^ h = φ s from hs]
    exact (Algebra.IsIntegral.isIntegral s).map φ.toRatAlgHom
  have h2 : FiniteDimensional ℚ (imField φ) :=
    (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional
  have h3 : FiniteDimensional ℚ (imField φ ⊔ IntermediateField.adjoin ℚ R : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_sup _ _
  have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ R := fun x =>
    (le_sup_left : imField φ ≤ _) ⟨x, rfl⟩
  have hz : ∀ s ∈ insert 1 S, ∀ z : ℂ, z ^ h = φ s → z ∈ imField φ ⊔ IntermediateField.adjoin ℚ R :=
    fun s hs z hz => (le_sup_right : IntermediateField.adjoin ℚ R ≤ _)
      (IntermediateField.subset_adjoin ℚ R (Set.mem_iUnion₂.2 ⟨s, hs, hz⟩))
  have hle : kummerField φ h ≤ imField φ ⊔ IntermediateField.adjoin ℚ R := by
    refine (kummerField_le_iff φ).2 ⟨hE, hz 1 (Set.mem_insert _ _) _ ?_, fun y hy z hzy => ?_⟩
    · rw [map_one]
      exact (Complex.isPrimitiveRoot_exp h h0).pow_eq_one
    · obtain ⟨s, hs, x, rfl⟩ := H y hy
      have hx : φ x ≠ 0 := by
        rw [map_ne_zero]
        rintro rfl
        exact hy.1 (by rw [zero_pow h0, zero_mul])
      have h4 := hz s (Set.mem_insert_of_mem _ hs) (z / φ x) (by
        rw [div_pow, hzy, map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hx)])
      simpa [hx] using mul_mem h4 (hE x)
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

end GlobalTheory.Mem.FieldsEx

end
