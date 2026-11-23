import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HensNbhd

theorem exists_finite_etale_of_etale (R : Type) [CommRing R] [HenselianLocalRing R]
    [IsNoetherianRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] (hq : q.comap (algebraMap R A) = maximalIdeal R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ),
      ρ.Finite ∧ ρ.Etale ∧ (maximalIdeal R).map ρ = maximalIdeal R' ∧
      (letI := (ResidueField.map ρ).toAlgebra; Algebra.IsSeparable (ResidueField R) (ResidueField R')) ∧
      (IsAdicComplete (maximalIdeal R) R → IsAdicComplete (maximalIdeal R') R') ∧
      ∃ ψ : A →+* R', ψ.comp (algebraMap R A) = ρ := by
  let Aq := Localization.AtPrime q
  haveI : IsLocalHom (algebraMap R Aq) := by
    refine ⟨fun r hr => ?_⟩
    rw [IsScalarTower.algebraMap_apply R A Aq, IsLocalization.AtPrime.isUnit_to_map_iff Aq q] at hr
    rw [← IsLocalRing.notMem_maximalIdeal, ← hq]
    exact hr
  haveI : Algebra.FormallyUnramified R Aq := Algebra.FormallyUnramified.comp R A Aq
  haveI : Algebra.EssFiniteType R Aq := Algebra.EssFiniteType.comp R A Aq
  obtain ⟨R', _, _, hfin, het, hloc, ⟨ε⟩⟩ := exists_etale_lift_of_isSeparable R (ResidueField Aq)
  haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'
  haveI : IsLocalHom (algebraMap R R') :=
    ((local_hom_TFAE (algebraMap R R')).out 0 4).mpr (comap_eq_maximalIdeal_of_finite _)
  let g1 : A →ₐ[R] ResidueField Aq :=
    (IsScalarTower.toAlgHom R Aq (ResidueField Aq)).comp (IsScalarTower.toAlgHom R A Aq)
  let g2 : ResidueField R ⊗[R] R' →ₐ[R] ResidueField R' :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField R'))
      (IsScalarTower.toAlgHom R R' (ResidueField R')) (fun _ _ => Commute.all _ _)
  let φ : A →ₐ[R] R' ⧸ maximalIdeal R' := (g2.comp (ε.symm.restrictScalars R).toAlgHom).comp g1
  obtain ⟨ψ, -⟩ := exists_algHom_lift_of_etale_of_isLocalRing (maximalIdeal R') φ
  have hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' :=
    Algebra.FormallyUnramified.map_maximalIdeal
  refine ⟨R', inferInstance, inferInstance, algebraMap R R', inferInstance,
    RingHom.finite_algebraMap.mpr hfin, ?_, hm, ?_, fun hc => ?_, ψ.toRingHom, ψ.comp_algebraMap⟩
  · exact RingHom.etale_algebraMap.mpr het
  · have h : (ResidueField.map (algebraMap R R')).toAlgebra =
        (inferInstance : Algebra (ResidueField R) (ResidueField R')) :=
      Algebra.algebra_ext _ _ fun r => by
        obtain ⟨x, rfl⟩ := residue_surjective r
        rfl
    exact h ▸ (inferInstance : Algebra.IsSeparable (ResidueField R) (ResidueField R'))
  · have := isAdicComplete_map_of_finite (maximalIdeal R) R'
    rwa [hm] at this

theorem exists_finite_etale_section : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsNoetherianRing R] (U : Scheme.{0}) (u : U ⟶ Sp R),
    Etale u → closedPoint R ∈ Set.range u →
    ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ),
      ρ.Finite ∧ ρ.Etale ∧ (maximalIdeal R).map ρ = maximalIdeal R' ∧
      (letI := (ResidueField.map ρ).toAlgebra; Algebra.IsSeparable (ResidueField R) (ResidueField R')) ∧
      (IsAdicComplete (maximalIdeal R) R → IsAdicComplete (maximalIdeal R') R') ∧
      ∃ σ : Sp R' ⟶ U, σ ≫ u = spMap ρ := by
  intro R _ _ _ U u hu ⟨s, hs⟩
  obtain ⟨V, hV, hsV, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (show s ∈ (⊤ : U.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  obtain ⟨t, rfl⟩ : s ∈ Set.range hV'.fromSpec := by rw [hV'.range_fromSpec]; exact hsV
  let f := hV'.fromSpec ≫ u
  have hf : Etale f := inferInstance
  let φ := Spec.preimage f
  have hφ : Spec.map φ = f := Spec.map_preimage f
  have het : RingHom.Etale φ.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; exact hf
  letI := φ.hom.toAlgebra
  haveI : Algebra.Etale R Γ(U, V) := het
  have hq : t.asIdeal.comap (algebraMap R Γ(U, V)) = maximalIdeal R := by
    have h1 : (Spec.map φ) t = closedPoint R := by
      rw [hφ, ← hs]; rfl
    exact congrArg PrimeSpectrum.asIdeal h1
  haveI : t.asIdeal.IsPrime := t.isPrime
  obtain ⟨R', i1, i2, ρ, i3, h1, h2, h3, h4, h5, ψ, hψ⟩ :=
    exists_finite_etale_of_etale R Γ(U, V) t.asIdeal hq
  refine ⟨R', i1, i2, ρ, i3, h1, h2, h3, h4, h5, Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec, ?_⟩
  rw [Category.assoc]
  change Spec.map (CommRingCat.ofHom ψ) ≫ f = _
  rw [← hφ, ← Spec.map_comp, ← hψ]
  rfl

end GlobalTheory.HensNbhd
