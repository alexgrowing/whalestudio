import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis

theorem exists_extend_of_isAlgebraic {A B F : Type} [Field A] [Field B] [Field F] [IsAlgClosed F] [Algebra A B]
    [Algebra.IsAlgebraic A B] (g : A →+* F) : ∃ σ : B →+* F, ∀ x, σ (algebraMap A B x) = g x := by
  letI : Algebra A F := g.toAlgebra
  let σ : B →ₐ[A] F := IsAlgClosed.lift
  exact ⟨(σ : B →+* F), fun x => σ.commutes x⟩

theorem exists_finite_normal_containing : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [CharZero R₁], IsIntegrallyClosed R₁ → ∀ (I : Type) [Finite I] (Φ : I → AlgebraicClosure (FractionRing R₁)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂) (j : FractionRing R₂ →+* AlgebraicClosure (FractionRing R₁)) (Φ₂ : I → FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ (∀ x, j (h' x) = algebraMap (FractionRing R₁) _ x) ∧ (∀ i, j (Φ₂ i) = Φ i) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (ga : FractionRing R₂ →+* F), ∃ σ : AlgebraicClosure (FractionRing R₁) →+* F, ∀ x, σ (j x) = ga x := by
  intro R₁ _ _ _ _ hIC I _ Φ
  let K := FractionRing R₁
  let L := AlgebraicClosure K
  let K₂ : IntermediateField K L := IntermediateField.adjoin K (Set.range Φ)
  haveI : Finite (Set.range Φ) := (Set.finite_range Φ).to_subtype
  haveI : FiniteDimensional K K₂ :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R₁
  haveI : Algebra.IsSeparable K K₂ := inferInstance
  let R₂ := integralClosure R₁ K₂
  haveI : IsFractionRing R₂ K₂ := IsIntegralClosure.isFractionRing_of_finite_extension R₁ K K₂ R₂
  haveI hfin : Module.Finite R₁ R₂ := IsIntegralClosure.finite R₁ K K₂ R₂
  let e : FractionRing R₂ ≃ₐ[R₂] K₂ := FractionRing.algEquiv R₂ K₂
  have hinj : Function.Injective (algebraMap R₁ K₂) := by
    rw [IsScalarTower.algebraMap_eq R₁ K K₂]
    exact (algebraMap K K₂).injective.comp (IsFractionRing.injective R₁ K)
  refine ⟨R₂, inferInstance, inferInstance, algebraMap R₁ R₂,
    (e.symm : K₂ →+* FractionRing R₂).comp (algebraMap K K₂),
    (algebraMap K₂ L).comp (e : FractionRing R₂ →+* K₂),
    fun i => e.symm ⟨Φ i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply hinj
    rw [IsScalarTower.algebraMap_apply R₁ R₂ K₂ a, IsScalarTower.algebraMap_apply R₁ R₂ K₂ b, hab]
  · exact RingHom.finite_algebraMap.mpr hfin
  · exact integralClosure.isIntegrallyClosedOfFiniteExtension K
  · intro r
    change e.symm (algebraMap K K₂ (algebraMap R₁ K r)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₁ R₂ K₂, AlgEquiv.commutes]
  · intro x
    change algebraMap K₂ L (e (e.symm (algebraMap K K₂ x))) = _
    rw [e.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  · intro i
    change algebraMap K₂ L (e (e.symm _)) = _
    rw [e.apply_symm_apply]; rfl
  · intro F _ _ ga
    haveI : Algebra.IsAlgebraic K₂ L := Algebra.IsAlgebraic.tower_top (K := K) K₂
    obtain ⟨σ, hσ⟩ := exists_extend_of_isAlgebraic (A := K₂) (B := L) (ga.comp (e.symm : K₂ →+* FractionRing R₂))
    refine ⟨σ, fun x => (hσ (e x)).trans ?_⟩
    exact congrArg ga (e.symm_apply_apply x)

end GlobalTheory.OneBasis
