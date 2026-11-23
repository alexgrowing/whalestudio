import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCongrOfResidueFixedByDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingFixedFieldInertiaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertiaStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsSchemeModelDescentUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfUnramifiedAbelianSchemeModelStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C5
open GlobalTheory

theorem val_lt_one_iff {F : Type} [Field F] (A : ValuationSubring F) {x : F} (hx : x ≠ 0) :
    A.valuation x < 1 ↔ x⁻¹ ∉ A := by
  rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]

end UpperTheory.Lit.Nos.C5

theorem UpperTheory.Lit.Nos.C5.mapsTo_fixedField_inertia : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω), σ • V = V → ∀ x ∈ IntermediateField.fixedField (inertia K V), σ x ∈ IntermediateField.fixedField (inertia K V) := by
  intro K Ω _ _ _ V σ hσ x hx
  have hσinv : σ⁻¹ • V = V := by
    conv_lhs => rw [← hσ]
    exact inv_smul_smul σ V
  have hmem : ∀ (ρ : Ω ≃ₐ[K] Ω), ρ • V = V → ∀ y, ρ y ∈ V ↔ y ∈ V := by
    intro ρ h y
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := ρ) (S := V) (x := y), h]
    rfl
  have hval : ∀ (ρ : Ω ≃ₐ[K] Ω), ρ • V = V → ∀ w, V.valuation (ρ w) < 1 ↔ V.valuation w < 1 := by
    intro ρ h w
    by_cases hw : w = 0
    · simp [hw]
    · rw [UpperTheory.Lit.Nos.C5.val_lt_one_iff V hw, UpperTheory.Lit.Nos.C5.val_lt_one_iff V ((map_ne_zero ρ).2 hw), ← map_inv₀, hmem ρ h]
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro τ hτ
  have hρ : σ⁻¹ * τ * σ ∈ inertia K V := by
    rw [mem_inertia_iff] at hτ ⊢
    obtain ⟨h1, h2⟩ := hτ
    refine ⟨?_, fun y hy => ?_⟩
    · rw [mul_smul, mul_smul, hσ, h1, hσinv]
    · have hz : σ y ∈ V := (hmem σ hσ y).2 hy
      have e : (σ⁻¹ * τ * σ) y - y = σ⁻¹ (τ (σ y) - σ y) := by
        rw [map_sub]
        simp [AlgEquiv.mul_apply]
      rw [e, hval σ⁻¹ hσinv]
      exact h2 _ hz
  have := hx _ hρ
  have e2 : τ (σ x) = σ ((σ⁻¹ * τ * σ) x) := by simp [AlgEquiv.mul_apply]
  rw [e2, this]

theorem UpperTheory.Lit.Nos.C5.hasGoodReduction_of_inertiaFixed : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → HasGoodReduction (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ((Over.pullback (spMap (algebraMap K (IntermediateField.fixedField (inertia K V))))).obj A) → HasGoodReduction R K A := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA hgood
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set W := V.comap (algebraMap K' Ω) with hW
  haveI : IsDiscreteValuationRing W := GlobalTheory.T.isDiscreteValuationRing_fixedField_inertia_alt R K Ω V hV
  have memW : ∀ z : K', z ∈ W ↔ algebraMap K' Ω z ∈ V := fun z => ValuationSubring.mem_comap
  have e1 : ∀ a : K, algebraMap K' Ω (algebraMap K K' a) = algebraMap K Ω a :=
    fun a => (IsScalarTower.algebraMap_apply K K' Ω a).symm
  have hRW : ∀ r : R, algebraMap K K' (algebraMap R K r) ∈ W := by
    intro r
    rw [memW, e1]
    have h1 : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact h1
  letI : Algebra R W := (((algebraMap K K').comp (algebraMap R K)).codRestrict W hRW).toAlgebra
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R W K' := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hmax : ∀ x : W, x ∈ maximalIdeal W ↔ V.valuation (algebraMap K' Ω x) < 1 := by
    intro x
    rw [ValuationSubring.valuation_lt_one_iff]
    by_cases hx : (x : K') = 0
    · simp [hx]
    · have hx' : algebraMap K' Ω x ≠ 0 := (map_ne_zero _).2 hx
      rw [UpperTheory.Lit.Nos.C5.val_lt_one_iff W hx, UpperTheory.Lit.Nos.C5.val_lt_one_iff V hx', memW, map_inv₀]
  have hunr : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨hlt, hdiv⟩ := GlobalTheory.T.uniformizer_of_valuationRing_fixedField_inertia R K Ω V hV π hπ
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap R W π ∈ maximalIdeal W
      rw [hmax]
      show V.valuation (algebraMap K' Ω (algebraMap K K' (algebraMap R K π))) < 1
      rw [e1]; exact hlt
    · intro x hx
      rw [hmax] at hx
      obtain ⟨z, hzV, hz⟩ := hdiv (x : K') hx
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨z, (memW z).2 hzV⟩, Subtype.ext ?_⟩
      show z * algebraMap K K' (algebraMap R K π) = (x : K')
      rw [hz, mul_comm]
  have hσinv : ∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → σ⁻¹ • V = V := by
    intro σ h
    conv_lhs => rw [← h]
    exact inv_smul_smul σ V
  have hσmem : ∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → ∀ x, σ x ∈ V ↔ x ∈ V := by
    intro σ h x
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := V) (x := x), h]
    rfl
  let res : ∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → (K' ≃ₐ[K] K') := fun σ h =>
    { toFun := fun x => ⟨σ (x : Ω), UpperTheory.Lit.Nos.C5.mapsTo_fixedField_inertia K Ω V σ h x x.2⟩
      invFun := fun x => ⟨σ.symm (x : Ω), UpperTheory.Lit.Nos.C5.mapsTo_fixedField_inertia K Ω V σ⁻¹ (hσinv σ h) x x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : Ω))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : Ω))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : Ω) (y : Ω))
      map_add' := fun x y => Subtype.ext (map_add σ (x : Ω) (y : Ω))
      commutes' := fun a => Subtype.ext (σ.commutes a) }
  let D : Set (K' ≃ₐ[K] K') := {τ | ∃ σ : Ω ≃ₐ[K] Ω, σ • V = V ∧ ∀ x : K', algebraMap K' Ω (τ x) = σ (algebraMap K' Ω x)}
  have hD1 : ∀ σ : K' ≃ₐ[K] K', σ ∈ D → ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y := by
    rintro τ ⟨σ, hσ, hτ⟩ x
    refine ⟨⟨τ x, ?_⟩, rfl⟩
    rw [memW, hτ, hσmem σ hσ, ← memW]
    exact x.2
  have hD2 : ∀ σ : K' ≃ₐ[K] K', σ ∈ D → ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y := by
    rintro τ ⟨σ, hσ, hτ⟩ x
    refine ⟨⟨τ.symm x, ?_⟩, rfl⟩
    have h2 : σ (algebraMap K' Ω (τ.symm x)) = algebraMap K' Ω x := by
      rw [← hτ, τ.apply_symm_apply]
    rw [memW, ← hσmem σ hσ, h2, ← memW]
    exact x.2
  have hres : ∀ x : W, (∀ σ : K' ≃ₐ[K] K', σ ∈ D → ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) →
      ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W := by
    intro x H
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_dvr_congr_of_residue_fixed_by_decomposition R K Ω V hV (algebraMap K' Ω x) ((memW x).1 x.2) (fun σ hσ => by
      have hτD : res σ hσ ∈ D := ⟨σ, hσ, fun _ => rfl⟩
      have hy : (res σ hσ x : K') ∈ W := by
        rw [memW]; exact (hσmem σ hσ _).2 ((memW x).1 x.2)
      have h3 := (hmax _).1 (H (res σ hσ) hτD ⟨_, hy⟩ rfl)
      exact h3)
    refine ⟨r, (hmax _).2 ?_⟩
    exact hr
  obtain ⟨G, _, hG, e, he⟩ := hgood
  obtain ⟨X, a, g, ha, hg, hc⟩ := UpperTheory.Lit.Nos.C4.exists_scheme_model_descent_unramified R K W K' hunr D hD1 hD2 hres A hA G hG e he
  exact GlobalTheory.T.hasGoodReduction_of_unramified_abelianScheme_model R K W K' hunr A hA G hG e he X a g ha hg hc
