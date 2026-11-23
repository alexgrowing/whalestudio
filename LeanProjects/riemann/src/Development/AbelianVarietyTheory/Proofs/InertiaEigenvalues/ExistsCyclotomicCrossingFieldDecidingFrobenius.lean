import Mathlib
import ReciprocityTheory.GaloisValuations.Global
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.ChebCross

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem autToPow_eq_iff {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (f : Ω ≃ₐ[F] Ω)
    (j : (ZMod m)ˣ) : hζ.autToPow F f = j ↔ f ζ = ζ ^ (j : ZMod m).val := by
  constructor
  · rintro rfl
    exact (hζ.autToPow_spec F f).symm
  · intro h
    rw [← hζ.autToPow_spec F f] at h
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h
    exact Units.ext (ZMod.val_injective m this)

theorem exists_fixing [CharZero Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (hirr : Irreducible (cyclotomic m L))
    (j : (ZMod m)ˣ) : ∃ u : Ω ≃ₐ[F] Ω, u ∈ L.fixingSubgroup ∧ hζ.autToPow F u = j := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  haveI : CharZero L := (algebraMap L Ω).charZero
  have hj : IsPrimitiveRoot (ζ ^ (j : ZMod m).val) m :=
    hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime j)
  have h1 : minpoly L (ζ ^ (j : ZMod m).val) = minpoly L ζ := by
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
      ← hj.minpoly_eq_cyclotomic_of_irreducible hirr]
  obtain ⟨u, hu⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := L) Ω).1 h1
  refine ⟨u.restrictScalars F, ?_, ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact u.commutes ⟨x, hx⟩
  · rw [autToPow_eq_iff]
    exact hu

theorem irreducible_of_onto [CharZero Ω] (Z : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m)
    (h : ∀ j : (ZMod m)ˣ, ∃ u : Ω ≃ₐ[F] Ω, u ∈ Z.fixingSubgroup ∧ hζ.autToPow F u = j) :
    Irreducible (cyclotomic m Z) := by
  classical
  haveI : CharZero Z := (algebraMap Z Ω).charZero
  have hm : 0 < m := NeZero.pos m
  have h0 : aeval ζ (cyclotomic m Z) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hm
  have hint : IsIntegral Z ζ := ⟨_, cyclotomic.monic m Z, h0⟩
  have hdvd := minpoly.dvd Z ζ h0
  have hsub : primitiveRoots m Ω ⊆ ((minpoly Z ζ).aroots Ω).toFinset := by
    intro μ hμ
    rw [mem_primitiveRoots hm] at hμ
    obtain ⟨i, hi, hic, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ
    obtain ⟨u, hu, hj⟩ := h (ZMod.unitOfCoprime i hic)
    rw [autToPow_eq_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi] at hj
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    let v : Ω ≃ₐ[Z] Ω := Z.fixingSubgroupEquiv ⟨u, hu⟩
    have hv : v ζ = ζ ^ i := hj
    rw [← hv, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdeg : (cyclotomic m Z).natDegree ≤ (minpoly Z ζ).natDegree := by
    rw [natDegree_cyclotomic, ← hζ.card_primitiveRoots]
    refine (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ?_)
    refine (card_roots' _).trans ?_
    exact natDegree_map_le
  have := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m Z) hdvd hdeg
  rw [this]
  exact minpoly.irreducible hint

theorem exists_pow_eq_on (M : IntermediateField F Ω) [FiniteDimensional F M] [IsGalois F M]
    (h σ : Ω ≃ₐ[F] Ω)
    (hσ : σ ∈ (M ⊓ IntermediateField.fixedField (Subgroup.zpowers h)).fixingSubgroup) :
    ∃ k : ℕ, ∀ x ∈ M, σ x = (h ^ k) x := by
  let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M
  have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : M), ((ρ f x : M) : Ω) = f x := fun f x =>
    AlgEquiv.restrictNormal_commutes f M x
  have h1 : ρ σ ∈ Subgroup.zpowers (ρ h) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (ρ h)),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply Subtype.ext
    rw [hρ]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    refine hσ _ ⟨x.2, ?_⟩
    change (x : Ω) ∈ IntermediateField.fixedField (Subgroup.zpowers h)
    rw [IntermediateField.mem_fixedField_iff]
    rintro f ⟨n, rfl⟩
    have := hx (ρ (h ^ n)) ⟨n, by simp⟩
    rw [← hρ, this]
  rw [← mem_powers_iff_mem_zpowers] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨k, fun x hx => ?_⟩
  have := hρ σ ⟨x, hx⟩
  rw [← hk] at this
  simp only [← map_pow] at this
  rw [hρ] at this
  exact this.symm

theorem cross : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : G F Ω) (m : ℕ), m.Prime → Module.finrank F L ∣ m - 1 → Irreducible (cyclotomic m L) → ∃ (Z : IntermediateField F Ω) (τ : (ZMod m)ˣ), FiniteDimensional F Z ∧ Irreducible (cyclotomic m Z) ∧ ∀ σ : G F Ω, σ ∈ Z.fixingSubgroup → (∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ (τ : ZMod m).val) → σ * g⁻¹ ∈ L.fixingSubgroup := by
  intro F Ω _ _ _ _ _ L _ _ g m hm hdiv hirr
  haveI : Fact m.Prime := ⟨hm⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod m)ˣ)
  obtain ⟨u, hu, hu'⟩ := exists_fixing L hζ hirr (τ * (hζ.autToPow F g)⁻¹)
  set h := u * g with hh
  have hχ : hζ.autToPow F h = τ := by rw [hh, map_mul, hu']; simp
  haveI : IsCyclotomicExtension {m} F (IntermediateField.adjoin F {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension F
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IsCyclotomicExtension.finiteDimensional {m} F _
  haveI : IsGalois F (IntermediateField.adjoin F {ζ}) := IsCyclotomicExtension.isGalois {m} F _
  let M : IntermediateField F Ω := L ⊔ IntermediateField.adjoin F {ζ}
  haveI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup _ _
  haveI : IsGalois F M := { }
  have hζM : ζ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.mem_adjoin_simple_self F ζ)
  refine ⟨M ⊓ IntermediateField.fixedField (Subgroup.zpowers h), τ, ?_, ?_, ?_⟩
  · exact Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : _ ≤ M)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  · refine irreducible_of_onto _ hζ fun j => ?_
    obtain ⟨n, rfl⟩ := hτ j
    refine ⟨h ^ n, ?_, by simp [hχ]⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixedField_iff _ _).1 hx.2 _ ⟨n, rfl⟩
  · intro σ hσ hσζ
    obtain ⟨k, hk⟩ := exists_pow_eq_on M h σ hσ
    have h1 : hζ.autToPow F (h ^ k) = τ := by
      rw [autToPow_eq_iff, ← hk ζ hζM]
      exact hσζ ζ hζ.pow_eq_one
    rw [map_pow, hχ] at h1
    have hord : orderOf τ = m - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]
    have hmod : k ≡ 1 [MOD m - 1] := by
      rw [← hord, ← pow_eq_pow_iff_modEq, h1, pow_one]
    let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L
    have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : L), ((ρ f x : L) : Ω) = f x := fun f x =>
      AlgEquiv.restrictNormal_commutes f L x
    have h2 : ρ σ = ρ (h ^ k) := by
      ext x
      rw [hρ, hρ]
      exact hk _ ((le_sup_left : L ≤ M) x.2)
    have h3 : ρ h ^ k = ρ h := by
      conv_rhs => rw [← pow_one (ρ h)]
      rw [pow_eq_pow_iff_modEq]
      refine hmod.of_dvd (dvd_trans ?_ hdiv)
      rw [← IsGalois.card_aut_eq_finrank]
      exact orderOf_dvd_natCard _
    have h4 : ρ u = 1 := by
      rw [← IntermediateField.restrictNormalHom_ker] at hu
      exact hu
    rw [← IntermediateField.restrictNormalHom_ker]
    change ρ (σ * g⁻¹) = 1
    rw [map_mul, h2, map_pow, h3, hh, map_mul, h4, map_inv]
    simp

end GlobalTheory.ChebCross
