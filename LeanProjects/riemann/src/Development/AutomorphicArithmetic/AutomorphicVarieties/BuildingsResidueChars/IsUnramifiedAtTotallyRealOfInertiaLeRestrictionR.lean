import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

theorem UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], (∀ (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Ine (F := Lp L) A ≤ (resP L Ω).range) → ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal := by
  intro L Ω _ _ _ _ _ _ h w
  obtain ⟨A, hA⟩ := exists_valuationSubring_over (Ω := Ω) w
  let v : Plc (Lp L) := ⟨w.asIdeal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)), inferInstance, by
    exact Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)) w.asIdeal)⟩
  have hv : IsPlaceOver A v := by
    intro x
    have h1 := hA (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    show _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) x ∈ w.asIdeal
    rw [← h1, IsScalarTower.algebraMap_apply (Lp L) L Ω]
    rfl
  have hle := h A v hv
  have hbot : Ideal.inertia Gal(L/(Lp L)) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs (Lp L) L Ω A w hA, eq_bot_iff]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, rfl⟩ := hle hσ
    rw [Subgroup.mem_bot]
    ext x
    apply (algebraMap L Ω).injective
    rw [AlgEquiv.one_apply]
    show algebraMap L Ω ((AlgEquiv.restrictScalars (Lp L) τ).restrictNormal L x) = _
    rw [AlgEquiv.restrictNormal_commutes]
    exact τ.commutes x
  refine Ideal.ramificationIdx_eq_one_iff.mp ?_
  rw [← (UpperTheory.V.CF.ineCard).1 (Lp L) L w, hbot]
  simp
