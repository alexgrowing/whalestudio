import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegFunctionFieldEq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.GenericCharts

theorem exists_etale_coords (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) (D : ℕ) (hp : IsProjOver p) (hd : topologicalKrullDim X = (D : ℕ)) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  obtain ⟨N, i, hi, hcomp⟩ := hp
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : LocallyOfFiniteType p := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ p)
  have hψ : Spec.map ψ = hU.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(X, U) := ψ.hom.toAlgebra
  haveI hft : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(X, U) = D :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F p hU ⟨_, hxU⟩ D hd
  haveI : FaithfulSMul F Γ(X, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(X, U)).injective
  obtain ⟨f, hf, hs⟩ := GlobalTheory.GenericEtale.exists_away F Γ(X, U) hA
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap Γ(X, U) B)) := IsOpenImmersion.of_isLocalization f
  let i' : Sp Γ(X, U) ⟶ X := hU.fromSpec
  haveI : IsOpenImmersion i' := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hi' : i' ≫ p = spMap (algebraMap F Γ(X, U)) := hψ.symm
  let j : Sp B ⟶ X := spMap (algebraMap Γ(X, U) B) ≫ i'
  have hj : j ≫ p = spMap (algebraMap F B) := by
    rw [Category.assoc, hi', IsScalarTower.algebraMap_eq F Γ(X, U) B, ← Spec.map_comp]
    rfl
  have h₁ : SmoothOfRelativeDimension D (j ≫ p) := by
    rw [hj]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).mpr ?_
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).mpr hs)
  have h₂ : SmoothOfRelativeDimension D (j.opensRange.ι ≫ p) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    have : SmoothOfRelativeDimension (0 + D) (j.isoOpensRange.inv ≫ j ≫ p) := inferInstance
    rwa [zero_add] at this
  refine ModelCharts.exists_etale_coords_of_opens p D j.opensRange ?_
  exact ⟨genericPoint _, genericPoint_eq_of_isOpenImmersion j⟩

theorem exists_generic_charts : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  intro F _ X _ _ p σ D hp hd
  haveI : CharZero F := σ.charZero
  obtain ⟨U, x, hU, hη, hx⟩ := exists_etale_coords F X p D hp hd
  exact ⟨U, hη, fun y hy => (AlgChart.exists_of_etale hU x hx hy).imp fun c h => h.1⟩

end GlobalTheory.GenericCharts
